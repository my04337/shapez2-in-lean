#!/usr/bin/env bash
# Lean REPL 起動スクリプト (macOS / Linux)
#
# 使い方:
#   .github/skills/lean-repl/scripts/repl.sh [--input <path>] [--rebuild-pickle] [--no-pickle]
#
# Persistent mode（デーモン常駐）:
#   repl.sh --start --session-id <id>                     セッション開始（import 完了まで待機）
#   repl.sh --send  --session-id <id> --cmd-file <path>   コマンド送信（応答を stdout に出力）
#   repl.sh --send  --session-id <id> --cmd '<json>'      単一コマンド送信
#   repl.sh --stop  --session-id <id>                     セッション停止
#
# --input モード（レガシー・エージェント向け）:
#   stdout には REPL の JSON 応答行のみを出力する。
#   ステータスメッセージは stderr に出力。
#   終了コード: 0=正常, 1=REPL応答にエラーあり, 2=REPLクラッシュ
#
# デフォルト動作: 'import S2IL' + 'import Mathlib.Tactic' + 'import Plausible' + 'import Duper' を先頭に自動挿入し env:0 を提供する。
# これにより ring, linarith, exact?, simp?, funext 等すべての Mathlib タクティク、plausible、duper が利用可能。
# 起動に約 16-20 秒かかる（Mathlib .olean 読み込みは初回のみ長め、以降はキャッシュ利用で高速化）。
#
# --no-pickle: 先頭への自動挿入を行わない。ユーザーが JSONL 内で import や unpickle を管理する。
# --rebuild-pickle: pickle ファイルを再生成する（カスタムセッション保存用途）。
# pickle ファイルは .repl/s2il.olean に保存される。

set -euo pipefail

# --- 引数解析 ---
INPUT=""
REBUILD_PICKLE=0
NO_PICKLE=0
# Persistent mode
MODE_START=0
MODE_SEND=0
MODE_STOP=0
SESSION_ID=""
CMD=""
CMD_FILE=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --input)          INPUT="$2"; shift 2 ;;
        --rebuild-pickle) REBUILD_PICKLE=1; shift ;;
        --no-pickle)      NO_PICKLE=1; shift ;;
        --start)          MODE_START=1; shift ;;
        --send)           MODE_SEND=1; shift ;;
        --stop)           MODE_STOP=1; shift ;;
        --session-id)     SESSION_ID="$2"; shift 2 ;;
        --cmd)            CMD="$2"; shift 2 ;;
        --cmd-file)       CMD_FILE="$2"; shift 2 ;;
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

    # S2IL + Mathlib.Tactic + Plausible + Duper をインポートして pickle を保存
    local import_cmd='{"cmd": "import S2IL\nimport Mathlib.Tactic\nimport Plausible\nimport Duper"}'
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

# ============================================================
#  Persistent モード関数群
# ============================================================

# --- olean ハッシュ（ビルド陳腐化検出）---
get_olean_hash() {
    local olean_dir="$REPO_ROOT/.lake/build/lib/lean/S2IL"
    if [[ ! -d "$olean_dir" ]]; then
        echo "none"
        return
    fi
    local files
    files=$(find "$olean_dir" -name '*.olean' -type f 2>/dev/null | sort)
    if [[ -z "$files" ]]; then
        echo "none"
        return
    fi
    # ファイル名:最終更新時刻 の連結文字列から SHA256 ハッシュを生成
    local combined=""
    while IFS= read -r f; do
        local mtime
        # macOS: stat -f %m, Linux: stat -c %Y
        if stat --version &>/dev/null; then
            mtime=$(stat -c '%Y' "$f" 2>/dev/null)
        else
            mtime=$(stat -f '%m' "$f" 2>/dev/null)
        fi
        combined="$combined$f:$mtime|"
    done <<< "$files"
    if command -v sha256sum &>/dev/null; then
        echo -n "$combined" | sha256sum | awk '{print $1}'
    elif command -v shasum &>/dev/null; then
        echo -n "$combined" | shasum -a 256 | awk '{print $1}'
    else
        # ハッシュコマンドなし → 常に陳腐化とみなす
        echo "no-hash-cmd"
    fi
}

# --- デーモン生存確認 ---
test_daemon_alive() {
    local session_dir="$1"
    local pid_file="$session_dir/daemon.pid"
    if [[ ! -f "$pid_file" ]]; then
        return 1
    fi
    local daemon_pid
    daemon_pid=$(cat "$pid_file" 2>/dev/null)
    if [[ -z "$daemon_pid" ]]; then
        return 1
    fi
    kill -0 "$daemon_pid" 2>/dev/null
}

# --- olean 陳腐化チェック ---
test_olean_stale() {
    local session_dir="$1"
    local hash_file="$session_dir/olean.hash"
    if [[ ! -f "$hash_file" ]]; then
        return 0  # ハッシュファイルなし → 陳腐化とみなす
    fi
    local saved_hash current_hash
    saved_hash=$(cat "$hash_file" 2>/dev/null)
    current_hash=$(get_olean_hash)
    [[ "$saved_hash" != "$current_hash" ]]
}

# --- セッション開始 ---
start_repl_session() {
    local session_dir="$REPL_DIR/$SESSION_ID"

    # 既に起動中かチェック
    if [[ -f "$session_dir/ready" ]]; then
        if test_daemon_alive "$session_dir"; then
            local daemon_pid
            daemon_pid=$(cat "$session_dir/daemon.pid" 2>/dev/null)
            echo "Session '$SESSION_ID' is already running (PID: $daemon_pid)" >&2
            return 0
        fi
        # ステートが古い → クリーンアップ
        rm -rf "$session_dir"
    fi

    # REPL バイナリ確認
    if ! test_repl_bin; then
        echo "REPL binary not found, building..." >&2
        lake build repl
        if [[ $? -ne 0 ]]; then
            return 1
        fi
    fi

    # セッションディレクトリ作成
    mkdir -p "$session_dir"

    # olean ハッシュ保存
    local hash
    hash=$(get_olean_hash)
    echo "$hash" > "$session_dir/olean.hash"

    # デーモンプロセス起動（バックグラウンド、nohup でシェル終了後も継続）
    local daemon_script="$SCRIPT_DIR/repl-daemon.sh"
    nohup "$daemon_script" --session-id "$SESSION_ID" --repo-root "$REPO_ROOT" \
        > "$session_dir/_daemon.log" 2>&1 &
    local daemon_launch_pid=$!

    echo "=== Persistent REPL: デーモン起動中 (PID: $daemon_launch_pid)... ===" >&2

    # ready シグナル待機（import 完了まで最大 120s）
    local ready_file="$session_dir/ready"
    local error_file="$session_dir/error"
    local elapsed=0
    local timeout_iterations=240  # 0.5s × 240 = 120s

    while [[ $elapsed -lt $timeout_iterations ]]; do
        if [[ -f "$ready_file" ]]; then
            echo "=== Persistent REPL: セッション '$SESSION_ID' 準備完了 ===" >&2
            return 0
        fi
        if [[ -f "$error_file" ]]; then
            local err_msg
            err_msg=$(cat "$error_file" 2>/dev/null)
            echo "Error: Daemon failed: $err_msg" >&2
            rm -rf "$session_dir"
            return 1
        fi
        # デーモンの異常終了チェック
        if ! kill -0 "$daemon_launch_pid" 2>/dev/null; then
            echo "Error: Daemon exited unexpectedly" >&2
            rm -rf "$session_dir"
            return 1
        fi
        sleep 0.5
        elapsed=$((elapsed + 1))  # 0.5s 刻みだが近似的にカウント
    done

    echo "Error: Daemon startup timed out (120s)" >&2
    kill "$daemon_launch_pid" 2>/dev/null || true
    rm -rf "$session_dir"
    return 1
}

# --- セッション停止 ---
stop_repl_session() {
    local session_dir="$REPL_DIR/$SESSION_ID"
    if [[ ! -d "$session_dir" ]]; then
        return 1
    fi

    # Shutdown シグナル
    echo "stop" > "$session_dir/shutdown"

    # デーモン終了待機（最大 5s）
    local pid_file="$session_dir/daemon.pid"
    if [[ -f "$pid_file" ]]; then
        local daemon_pid
        daemon_pid=$(cat "$pid_file" 2>/dev/null)
        if [[ -n "$daemon_pid" ]]; then
            local wait_count=0
            while [[ $wait_count -lt 25 ]]; do
                if ! kill -0 "$daemon_pid" 2>/dev/null; then
                    break
                fi
                sleep 0.2
                wait_count=$((wait_count + 1))
            done
            # まだ生きていれば強制終了
            if kill -0 "$daemon_pid" 2>/dev/null; then
                kill -9 "$daemon_pid" 2>/dev/null || true
            fi
        fi
    fi

    # REPL プロセスも確実に停止
    local repl_pid_file="$session_dir/repl.pid"
    if [[ -f "$repl_pid_file" ]]; then
        local repl_pid
        repl_pid=$(cat "$repl_pid_file" 2>/dev/null)
        if [[ -n "$repl_pid" ]] && kill -0 "$repl_pid" 2>/dev/null; then
            kill -9 "$repl_pid" 2>/dev/null || true
        fi
    fi

    rm -rf "$session_dir"
    return 0
}

# --- Send 処理 ---
send_to_session() {
    local session_dir="$REPL_DIR/$SESSION_ID"

    # コマンド内容の準備（Lazy Start の前にバリデーション）
    local cmd_content=""
    if [[ -n "$CMD_FILE" ]]; then
        if [[ ! -f "$CMD_FILE" ]]; then
            echo "Error: CmdFile not found: $CMD_FILE" >&2
            return 1
        fi
        cmd_content=$(cat "$CMD_FILE")
        cmd_content="${cmd_content%"${cmd_content##*[![:space:]]}"}"  # 末尾空白除去
    elif [[ -n "$CMD" ]]; then
        cmd_content="$CMD"
        cmd_content="${cmd_content%"${cmd_content##*[![:space:]]}"}"
        # JSON 構文チェック（基本的な検証）
        if command -v jq &>/dev/null; then
            local invalid=0
            while IFS= read -r jline; do
                local trimmed
                trimmed="${jline#"${jline%%[![:space:]]*}"}"
                [[ -z "$trimmed" ]] && continue
                if ! echo "$trimmed" | jq -e '.' &>/dev/null; then
                    echo "Error: -cmd の内容が有効な JSON ではありません: $trimmed" >&2
                    invalid=1
                fi
            done <<< "$cmd_content"
            if [[ $invalid -eq 1 ]]; then
                return 1
            fi
        fi
    fi

    if [[ -z "$cmd_content" ]]; then
        echo "Error: Empty command" >&2
        return 1
    fi

    # Lazy start: デーモンが起動していなければ自動起動
    if ! test_daemon_alive "$session_dir"; then
        echo "Daemon not running, starting..." >&2
        if ! start_repl_session; then
            return 1
        fi
    fi

    # Olean staleness: ビルド後は再起動
    if test_olean_stale "$session_dir"; then
        echo "olean files changed, restarting session..." >&2
        stop_repl_session
        if ! start_repl_session; then
            return 1
        fi
    fi

    # 古い応答シグナルをクリーンアップ
    local response_done="$session_dir/response.ready"
    local response_file="$session_dir/response.json"
    rm -f "$response_done" "$response_file"

    # リクエスト送信（アトミック書き込み: tmp → mv）
    local request_file="$session_dir/request.json"
    local temp_file="$request_file.tmp"
    echo "$cmd_content" > "$temp_file"
    mv -f "$temp_file" "$request_file"

    # 応答待機（最大 180s = 3 分、重いタクティク対応）
    local timeout_ms=180000
    local start_time
    start_time=$(date +%s%3N 2>/dev/null || echo $(($(date +%s) * 1000)))
    local elapsed_ms=0

    while [[ $elapsed_ms -lt $timeout_ms ]]; do
        if [[ -f "$response_done" ]]; then
            if [[ -f "$response_file" ]]; then
                local response
                response=$(cat "$response_file")

                # 各行を stdout に出力 + エラー検出
                local has_error=0
                while IFS= read -r rline; do
                    [[ -z "$rline" ]] && continue
                    echo "$rline"
                    # エラー検出
                    if echo "$rline" | grep -q '"severity"[[:space:]]*:[[:space:]]*"error"' 2>/dev/null; then
                        has_error=1
                    fi
                    if echo "$rline" | grep -q '"error"[[:space:]]*:' 2>/dev/null; then
                        has_error=1
                    fi
                    # tactic mode のエラー検出（"message" フィールド）
                    if echo "$rline" | grep -q '"message"[[:space:]]*:' 2>/dev/null; then
                        # "messages" は正常フィールドなので除外、"message" 単独は tactic エラー
                        if ! echo "$rline" | grep -q '"messages"' 2>/dev/null; then
                            has_error=1
                        fi
                    fi
                    # goals が存在する（証明未完了） → エラー扱い
                    if echo "$rline" | grep -q '"goals"[[:space:]]*:[[:space:]]*\[' 2>/dev/null; then
                        # goals が空配列 [] でなければエラー
                        if ! echo "$rline" | grep -q '"goals"[[:space:]]*:[[:space:]]*\[\]' 2>/dev/null; then
                            has_error=1
                        fi
                    fi
                done <<< "$response"

                rm -f "$response_done" "$response_file"
                return $has_error
            fi
        fi

        # デーモン生存確認
        if ! test_daemon_alive "$session_dir"; then
            echo "Error: Daemon died while waiting for response" >&2
            return 2
        fi

        sleep 0.03

        local current_time
        current_time=$(date +%s%3N 2>/dev/null || echo $(($(date +%s) * 1000)))
        elapsed_ms=$((current_time - start_time))
    done

    echo "Error: Response timed out (${timeout_ms}ms)" >&2
    return 2
}

# --- デフォルト起動コマンド（import ベース）---
# S2IL + Mathlib.Tactic + Plausible + Duper をインポートして env:0 を提供する。
# すべての Mathlib タクティク（ring, linarith, exact?, funext 等）、plausible、duper が利用可能になる。
get_init_cmd() {
    printf '{"cmd": "import S2IL\nimport Mathlib.Tactic\nimport Plausible\nimport Duper"}'
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

# ============================================================
#  Persistent REPL mode（--start / --send / --stop）
# ============================================================
if [[ $MODE_START -eq 1 || $MODE_SEND -eq 1 || $MODE_STOP -eq 1 ]]; then
    if [[ -z "$SESSION_ID" ]]; then
        echo "Error: --session-id is required for persistent mode" >&2
        exit 1
    fi

    if [[ $MODE_START -eq 1 ]]; then
        if start_repl_session; then
            exit 0
        else
            exit 1
        fi
    elif [[ $MODE_STOP -eq 1 ]]; then
        if stop_repl_session; then
            echo "=== Persistent REPL: セッション '$SESSION_ID' を停止しました ===" >&2
        else
            echo "=== Persistent REPL: セッション '$SESSION_ID' は起動されていません ===" >&2
        fi
        exit 0
    elif [[ $MODE_SEND -eq 1 ]]; then
        if [[ -z "$CMD" && -z "$CMD_FILE" ]]; then
            echo "Error: --cmd or --cmd-file is required for --send" >&2
            exit 1
        fi
        # --cmd と --cmd-file の同時指定時に警告
        if [[ -n "$CMD" && -n "$CMD_FILE" ]]; then
            echo "警告: --cmd と --cmd-file が同時に指定されました。--cmd-file が優先されます。" >&2
        fi
        send_to_session
        exit $?
    fi
fi

# ============================================================
#  バッチモード（レガシー）
# ============================================================

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
    # --- デフォルトモード: import S2IL + Mathlib.Tactic + Plausible + Duper を自動先頭挿入 ---
    # ring, linarith, exact?, funext 等すべての Mathlib タクティクが env:0 で利用可能。
    INIT_CMD="$(get_init_cmd)"

    if [[ -n "$INPUT" && -f "$INPUT" ]]; then
        USER_CONTENT="$(cat "$INPUT")"
        # ユーザー JSONL がすでに import コマンドで始まっている場合は重複挿入しない
        if echo "$USER_CONTENT" | grep -q '"cmd"[[:space:]]*:[[:space:]]*"import '; then
            FULL_INPUT="$USER_CONTENT"
        else
            FULL_INPUT="$(printf "%s\n\n%s" "$INIT_CMD" "$USER_CONTENT")"
        fi
        invoke_repl_with_crash_detect "$FULL_INPUT"
    else
        # インタラクティブモード
        echo "=== Lean REPL 起動（import S2IL + Mathlib.Tactic + Plausible + Duper） ===" >&2
        echo "JSON Lines 形式でコマンドを入力（Ctrl+D で終了）" >&2
        echo "起動後に import が完了するまで約 16-20 秒かかります。" >&2
        lake exe repl
    fi
else
    # --no-pickle モード: 自動先頭挿入なし（ユーザーが JSONL 内で import/unpickle を管理）
    if [[ -n "$INPUT" && -f "$INPUT" ]]; then
        invoke_repl_with_crash_detect "$(cat "$INPUT")"
    else
        echo "=== Lean REPL 起動（no-pickle: 自動先頭挿入なし） ===" >&2
        lake exe repl
    fi
fi

