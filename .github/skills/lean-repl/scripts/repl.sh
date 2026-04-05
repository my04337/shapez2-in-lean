#!/usr/bin/env bash
# Lean REPL 起動スクリプト (macOS / Linux)
#
# 使い方:
#   .github/skills/lean-repl/scripts/repl.sh [--input <path>] [--rebuild-pickle] [--no-pickle]
#
# --input モード（エージェント向け）:
#   stdout には REPL の JSON 応答行のみを 1 行 JSON で出力する。
#   ステータスメッセージは stderr に出力。
#   終了コード: 0=正常, 1=REPL応答にエラーあり, 2=REPLクラッシュ
#
# デフォルト動作: 'import S2IL' + 'import Mathlib.Tactic' を自動プレペンドし env:0 を提供する。
# これにより ring, linarith, exact?, simp?, funext 等すべての Mathlib タクティクが利用可能。
# 起動に約 16-20 秒かかる（Mathlib .olean 読み込みは初回のみ長め、以降はキャッシュ利用で高速化）。
#
# --no-pickle: 自動プレペンドを行わない。ユーザーが JSONL 内で import や unpickle を管理する。
# --rebuild-pickle: pickle ファイルを再生成する（カスタムセッション保存用途）。
# pickle ファイルは .repl/s2il.olean に保存される。

set -euo pipefail

# --- 引数解析 ---
INPUT=""
REBUILD_PICKLE=0
NO_PICKLE=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --input)     INPUT="$2"; shift 2 ;;
        --rebuild-pickle) REBUILD_PICKLE=1; shift ;;
        --no-pickle) NO_PICKLE=1; shift ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# --- パス解決 ---
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
REPL_DIR="$REPO_ROOT/.repl"
PICKLE_PATH="$REPL_DIR/s2il.olean"

cd "$REPO_ROOT"

# elan/lake を PATH に追加
if [[ -d "$HOME/.elan/bin" ]]; then
    export PATH="$HOME/.elan/bin:$PATH"
fi

# --- REPL バイナリの確認 ---
test_repl_bin() {
    [[ -f "$REPO_ROOT/.lake/build/bin/repl" ]]
}

# --- pickle 生成 ---
build_pickle() {
    local path="$1"
    echo "=== Lean REPL: pickle を生成中... ===" >&2
    mkdir -p "$(dirname "$path")"

    # S2IL + Mathlib.Tactic をインポートして pickle を保存
    local import_cmd='{"cmd": "import S2IL\nimport Mathlib.Tactic"}'
    local pickle_cmd
    pickle_cmd='{"pickleTo": "'"$path"'", "env": 0}'
    local commands
    commands="$(printf "%s\n\n%s" "$import_cmd" "$pickle_cmd")"

    local out
    if ! out=$(echo "$commands" | lake exe repl 2>&1); then
        echo "pickle 生成に失敗しました" >&2
        return 1
    fi

    if echo "$out" | grep -q '"severity":"error"'; then
        echo "pickle 生成中にエラーが発生しました:" >&2
        echo "$out" >&2
        return 1
    fi

    if [[ -f "$path" ]]; then
        echo "=== pickle 生成完了: $path ===" >&2
        return 0
    else
        echo "pickle ファイルが見つかりません: $path" >&2
        return 1
    fi
}

# --- デフォルト起動コマンド（import ベース）---
# S2IL + Mathlib.Tactic をインポートして env:0 を提供する。
# すべての Mathlib タクティク（ring, linarith, exact?, funext 等）が利用可能になる。
get_init_cmd() {
    printf '{"cmd": "import S2IL\nimport Mathlib.Tactic"}'
}

# --- JSON 出力処理 ---
# 空行区切りの複数行 JSON を 1 行に圧縮して stdout に出力。エラー検出も行う。
# 最終行に "json_count has_error" を出力する（呼び出し元がカウントを取得するため）。
emit_json_output() {
    local raw_file="$1"
    local has_error=0
    local json_count=0

    if command -v jq &>/dev/null; then
        while IFS= read -r line; do
            echo "$line"
            json_count=$((json_count + 1))
            if echo "$line" | jq -e '.messages[]? | select(.severity == "error")' &>/dev/null; then
                has_error=1
            fi
        done < <(
            # 空行区切りのチャンクを 1 行化
            awk 'BEGIN{RS=""; ORS="\n"} /^\{/{
                gsub(/\n/, " ")
                print
            }' "$raw_file" | jq -c '.' 2>/dev/null
        )
    else
        # jq なし: 空行区切りで結合して出力
        local chunk=""
        while IFS= read -r line || [[ -n "$line" ]]; do
            if [[ -z "$line" ]]; then
                if [[ -n "$chunk" ]]; then
                    local trimmed
                    trimmed="$(echo "$chunk" | tr -d '\n' | sed 's/^[[:space:]]*//')"
                    if [[ "$trimmed" == \{* ]]; then
                        echo "$trimmed"
                        json_count=$((json_count + 1))
                        if echo "$trimmed" | grep -q '"severity":"error"' 2>/dev/null || \
                           echo "$trimmed" | grep -q '"severity": "error"' 2>/dev/null; then
                            has_error=1
                        fi
                    fi
                    chunk=""
                fi
            else
                chunk="$chunk$line"
            fi
        done < "$raw_file"
        # 末尾の残りチャンク
        if [[ -n "$chunk" ]]; then
            local trimmed
            trimmed="$(echo "$chunk" | tr -d '\n' | sed 's/^[[:space:]]*//')"
            if [[ "$trimmed" == \{* ]]; then
                echo "$trimmed"
                json_count=$((json_count + 1))
                if echo "$trimmed" | grep -q '"severity":"error"' 2>/dev/null || \
                   echo "$trimmed" | grep -q '"severity": "error"' 2>/dev/null; then
                    has_error=1
                fi
            fi
        fi
    fi

    # 最終行にカウント情報（呼び出し元用）
    echo "$json_count $has_error"
}

# --- REPL 実行（クラッシュ検出付き）---
invoke_repl_with_crash_detect() {
    local full_input="$1"
    local input_cmd_count
    input_cmd_count=$(echo "$full_input" | grep -c '^\s*{' || true)

    local stderr_file raw_file output_file
    stderr_file="$(mktemp)"
    raw_file="$(mktemp)"
    output_file="$(mktemp)"

    set +e
    echo "$full_input" | lake exe repl >"$raw_file" 2>"$stderr_file"
    set -e

    # JSON 出力処理（最終行が "count hasError"）
    local last_line json_count has_error line_count
    emit_json_output "$raw_file" > "$output_file"
    last_line="$(tail -1 "$output_file")"
    json_count="$(echo "$last_line" | awk '{print $1}')"
    has_error="$(echo "$last_line" | awk '{print $2}')"

    # JSON 行のみ stdout に出力（最終行はカウント情報なので除く）
    line_count="$(wc -l < "$output_file")"
    if [[ "$line_count" -gt 1 ]]; then
        head -n -1 "$output_file"
    fi

    # クラッシュ検出: 応答数 < 入力コマンド数
    if [[ "$json_count" -lt "$input_cmd_count" ]]; then
        local missing crash_msg last_stderr
        missing=$((input_cmd_count - json_count))
        crash_msg="REPL process terminated unexpectedly. ${missing} command(s) were not processed."
        last_stderr="$(grep -v '^$' "$stderr_file" | tail -1 2>/dev/null || true)"
        if [[ -n "$last_stderr" ]]; then
            crash_msg="$crash_msg stderr: $last_stderr"
        fi
        printf '{"error":"repl_crashed","message":"%s","commands_sent":%d,"responses_received":%d}\n' \
            "$(echo "$crash_msg" | sed 's/"/\\"/g')" "$input_cmd_count" "$json_count"
        rm -f "$stderr_file" "$raw_file" "$output_file"
        exit 2
    fi

    rm -f "$stderr_file" "$raw_file" "$output_file"

    if [[ "$has_error" -eq 1 ]]; then
        exit 1
    else
        exit 0
    fi
}

# --- メイン処理 ---

# REPL バイナリが未ビルドならビルド（初回・lake clean 後などに必要。正常フロー）
if ! test_repl_bin; then
    echo "=== Lean REPL: バイナリをビルド中（初回・clean 後は自動ビルドします）... ===" >&2
    lake build repl
fi

# --rebuild-pickle: pickle ファイルを再生成して終了（--input も指定時は継続）
if [[ $REBUILD_PICKLE -eq 1 ]]; then
    if ! build_pickle "$PICKLE_PATH"; then
        echo "pickle 生成に失敗しました" >&2
        exit 1
    fi
    if [[ -z "$INPUT" ]]; then
        echo "=== pickle 再生成完了 ===" >&2
        exit 0
    fi
    # INPUT が指定されている場合は pickle 再生成後に通常実行を続ける
fi

if [[ $NO_PICKLE -eq 0 ]]; then
    # --- デフォルトモード: import S2IL + Mathlib.Tactic を自動プレペンド ---
    # ring, linarith, exact?, funext 等すべての Mathlib タクティクが env:0 で利用可能。
    INIT_CMD="$(get_init_cmd)"

    if [[ -n "$INPUT" && -f "$INPUT" ]]; then
        USER_CONTENT="$(cat "$INPUT")"
        # ユーザー JSONL がすでに import コマンドで始まっている場合は重複プレペンドしない
        if echo "$USER_CONTENT" | grep -q '"cmd"[[:space:]]*:[[:space:]]*"import '; then
            FULL_INPUT="$USER_CONTENT"
        else
            FULL_INPUT="$(printf "%s\n\n%s" "$INIT_CMD" "$USER_CONTENT")"
        fi
        invoke_repl_with_crash_detect "$FULL_INPUT"
    else
        # インタラクティブモード
        echo "=== Lean REPL 起動（import S2IL + Mathlib.Tactic） ===" >&2
        echo "JSON Lines 形式でコマンドを入力（Ctrl+D で終了）" >&2
        echo "起動後に import が完了するまで約 16-20 秒かかります。" >&2
        lake exe repl
    fi
else
    # --no-pickle モード: 自動プレペンドなし（ユーザーが JSONL 内で import/unpickle を管理）
    if [[ -n "$INPUT" && -f "$INPUT" ]]; then
        invoke_repl_with_crash_detect "$(cat "$INPUT")"
    else
        echo "=== Lean REPL 起動（no-pickle: 自動プレペンドなし） ===" >&2
        lake exe repl
    fi
fi

