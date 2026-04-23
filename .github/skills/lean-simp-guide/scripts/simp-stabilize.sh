#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 my04337
# SPDX-License-Identifier: MIT
#
# simp-stabilize.sh — bare simp → simp only 一括安定化パイプライン
#
# 使い方:
#   .github/skills/lean-simp-guide/scripts/simp-stabilize.sh --file S2IL/Behavior/Gravity.lean
#   .github/skills/lean-simp-guide/scripts/simp-stabilize.sh --file S2IL/Behavior/Gravity.lean --dry-run
#   .github/skills/lean-simp-guide/scripts/simp-stabilize.sh --file S2IL/Behavior/Gravity.lean --keep-backup
#
# 処理フロー:
#   1. 対象ファイルをバックアップ (.bak)
#   2. bare simp/simp_all → simp?/simp_all? に一括変換
#   3. lake env lean --json で位置付き提案を取得
#   4. 提案を行番号でマッピングし、ソースに適用
#   5. バックアップを削除（--keep-backup で保持可能）
#
# 注意:
#   - 対象ファイルが lake build でエラー 0 の状態から実行すること
#   - ネスト括弧パターン (simp [show ... from by ...]) は手動修正が必要
#   - 実行後は必ず lake build で検証すること
#
# 依存:
#   - lake (Lean/Elan)
#   - python3 または jq (JSON パース用)

set -euo pipefail

# --- ヘルパー ---

info() { printf '\033[36m[INFO] %s\033[0m\n' "$*" ;}
warn() { printf '\033[33m[WARN] %s\033[0m\n' "$*" ;}
ok()   { printf '\033[32m[ OK ] %s\033[0m\n' "$*" ;}
err()  { printf '\033[31m[ERR ] %s\033[0m\n' "$*" ;}

# --- 引数パース ---

FILE=""
DRY_RUN=0
KEEP_BACKUP=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --file)         FILE="$2"; shift 2 ;;
        --dry-run)      DRY_RUN=1; shift ;;
        --keep-backup)  KEEP_BACKUP=1; shift ;;
        *) err "不明なオプション: $1"; exit 1 ;;
    esac
done

# --- バリデーション ---

if [[ -z "$FILE" ]]; then
    err "--file は必須です"
    exit 1
fi

if [[ ! -f "$FILE" ]]; then
    err "ファイルが見つかりません: $FILE"
    exit 1
fi

# python3 または jq の存在確認
if command -v python3 &>/dev/null; then
    JSON_BACKEND="python3"
elif command -v jq &>/dev/null; then
    JSON_BACKEND="jq"
else
    err "JSON パースに python3 または jq が必要です"
    exit 1
fi

ABS_FILE=$(realpath "$FILE")
BAK_FILE="${ABS_FILE}.bak"

# --- Step 1: バックアップ ---

cp "$ABS_FILE" "$BAK_FILE"
info "バックアップ作成: $BAK_FILE"

cleanup() {
    if (( !KEEP_BACKUP )) && [[ -f "$BAK_FILE" ]]; then
        rm -f "$BAK_FILE"
    fi
}
trap cleanup EXIT

# --- Step 2: bare simp → simp? 変換 ---

CONVERT_COUNT=0
TMP_FILE="${ABS_FILE}.tmp"

while IFS= read -r line; do
    # simp only / simp_all only は安定化済み → スキップ
    if echo "$line" | grep -qE '\bsimp\s+only\b|\bsimp_all\s+only\b'; then
        printf '%s\n' "$line"
        continue
    fi

    # simp? / simp_all? は既にクエリ形式 → スキップ
    if echo "$line" | grep -qE '\bsimp(_all)?\?'; then
        printf '%s\n' "$line"
        continue
    fi

    # コメント行はスキップ
    if echo "$line" | grep -qE '^\s*--'; then
        printf '%s\n' "$line"
        continue
    fi

    NEW_LINE="$line"

    # simp_all → simp_all?
    if echo "$line" | grep -qE '\bsimp_all\b'; then
        NEW_LINE=$(echo "$line" | sed 's/\bsimp_all\b/simp_all?/g')
        if [[ "$NEW_LINE" != "$line" ]]; then
            (( CONVERT_COUNT++ ))
        fi
    fi

    # simp → simp? (simp_all? 変換後の行は除く)
    if [[ "$NEW_LINE" == "$line" ]] && echo "$line" | grep -qE '\bsimp\b'; then
        NEW_LINE=$(echo "$line" | sed 's/\bsimp\b/simp?/g')
        if [[ "$NEW_LINE" != "$line" ]]; then
            (( CONVERT_COUNT++ ))
        fi
    fi

    printf '%s\n' "$NEW_LINE"
done < "$ABS_FILE" > "$TMP_FILE"

# 末尾改行の調整（元ファイルに合わせる）
mv "$TMP_FILE" "$ABS_FILE"

info "bare simp → simp? 変換: $CONVERT_COUNT 件"

if (( CONVERT_COUNT == 0 )); then
    ok "安定化対象なし。終了します。"
    exit 0
fi

if (( DRY_RUN )); then
    warn "DryRun: simp? 変換のみ実行。lean --json は実行しません。"
    cp "$BAK_FILE" "$ABS_FILE"
    exit 0
fi

# --- Step 3: lean --json で提案取得 ---

info "lean --json 実行中... (数分かかる場合があります)"

export PATH="${HOME}/.elan/bin:${PATH}"

JSON_OUTPUT=$(lake env lean --json "$FILE" 2>/dev/null || true)

# --- Step 4: 提案をパース ---

parse_suggestions_python() {
    python3 - <<'PYEOF'
import sys, json

data = sys.stdin.read()
suggestions = {}  # {line_num: [suggestion, ...]}

for raw_line in data.splitlines():
    raw_line = raw_line.strip()
    if not raw_line:
        continue
    try:
        obj = json.loads(raw_line)
    except json.JSONDecodeError:
        continue
    if obj.get("severity") != "info":
        continue
    msg = obj.get("data", "")
    if "Try this:" not in msg:
        continue
    line_num = obj.get("pos", {}).get("line")
    if line_num is None:
        continue
    # Try this: の後の部分を取得
    idx = msg.index("Try this:")
    suggestion = msg[idx + len("Try this:"):].strip()
    # "[apply] " プレフィックスを除去
    if suggestion.startswith("[apply] "):
        suggestion = suggestion[len("[apply] "):]
    suggestion = suggestion.strip()
    if line_num not in suggestions:
        suggestions[line_num] = []
    suggestions[line_num].append(suggestion)

for ln, suggs in sorted(suggestions.items()):
    for s in suggs:
        # line_num TAB suggestion として出力
        print(f"{ln}\t{s}")
PYEOF
}

parse_suggestions_jq() {
    echo "$1" | jq -r 'select(.severity == "info") | select(.data | contains("Try this:")) | "\(.pos.line)\t\(.data | split("Try this:")[1] | ltrimstr(" [apply] ") | ltrimstr(" ") | rtrimstr("\n"))"' 2>/dev/null || true
}

PARSED_SUGGESTIONS=""
if [[ "$JSON_BACKEND" == "python3" ]]; then
    PARSED_SUGGESTIONS=$(echo "$JSON_OUTPUT" | parse_suggestions_python)
else
    PARSED_SUGGESTIONS=$(parse_suggestions_jq "$JSON_OUTPUT")
fi

TOTAL_SUGGESTIONS=$(echo "$PARSED_SUGGESTIONS" | grep -c '.' || true)
UNIQUE_LINES=$(echo "$PARSED_SUGGESTIONS" | awk -F'\t' '{print $1}' | sort -u | grep -c '.' || true)
info "提案取得: ${TOTAL_SUGGESTIONS} 件 (${UNIQUE_LINES} ユニーク行)"

# --- Step 5: 提案をソースに適用 ---

# バックアップから元ソースを読み直し
mapfile -t ORIG_LINES < "$BAK_FILE"

APPLIED_COUNT=0
SKIPPED_COUNT=0
declare -A LINE_SUGGESTIONS  # line_num -> tab-separated suggestions

# 行ごとに提案を収集
while IFS=$'\t' read -r ln sugg; do
    [[ -z "$ln" || -z "$sugg" ]] && continue
    if [[ -z "${LINE_SUGGESTIONS[$ln]+x}" ]]; then
        LINE_SUGGESTIONS[$ln]="$sugg"
    else
        LINE_SUGGESTIONS[$ln]="${LINE_SUGGESTIONS[$ln]}"$'\x00'"$sugg"
    fi
done <<< "$PARSED_SUGGESTIONS"

declare -a RESULT_LINES
for (( i=0; i<${#ORIG_LINES[@]}; i++ )); do
    RESULT_LINES[$i]="${ORIG_LINES[$i]}"
done

for ln in $(echo "${!LINE_SUGGESTIONS[@]}" | tr ' ' '\n' | sort -n); do
    IDX=$(( ln - 1 ))
    [[ $IDX -lt 0 || $IDX -ge ${#ORIG_LINES[@]} ]] && continue

    ORIG_LINE="${ORIG_LINES[$IDX]}"

    # 既に simp only なら飛ばす
    if echo "$ORIG_LINE" | grep -qE '\bsimp(_all)?\s+only\b'; then
        continue
    fi

    # ネスト括弧チェック（手動修正が必要）
    if echo "$ORIG_LINE" | grep -qE 'simp\s*\[.*show\s.*from\s.*by\b'; then
        warn "  L${ln}: ネスト括弧パターン（手動修正が必要）"
        (( SKIPPED_COUNT++ ))
        continue
    fi

    # インデント取得
    INDENT=""
    if [[ "$ORIG_LINE" =~ ^([[:space:]]+) ]]; then
        INDENT="${BASH_REMATCH[1]}"
    fi

    # <;> プレフィックス取得
    PREFIX=""
    if [[ "$ORIG_LINE" =~ (\<\;\>\s*) ]]; then
        PREFIX="${BASH_REMATCH[1]}"
    fi

    # at ターゲット取得
    AT_TARGET=""
    if [[ "$ORIG_LINE" =~ [[:space:]]at[[:space:]]([a-zA-Z_][a-zA-Z0-9_\']*) ]]; then
        AT_TARGET=" at ${BASH_REMATCH[1]}"
    fi

    RAW_SUGGS="${LINE_SUGGESTIONS[$ln]}"
    IFS=$'\x00' read -ra SUGG_LIST <<< "$RAW_SUGGS"

    if (( ${#SUGG_LIST[@]} > 1 )); then
        # 複数提案: 補題を union マージ
        BASE_CMD=""
        declare -A LEMMA_SET
        for sugg in "${SUGG_LIST[@]}"; do
            if [[ "$sugg" =~ (simp(_all)?[[:space:]]+only)[[:space:]]*\[([^\]]*)\] ]]; then
                [[ -z "$BASE_CMD" ]] && BASE_CMD="${BASH_REMATCH[1]}"
                IFS=',' read -ra LEMMAS <<< "${BASH_REMATCH[3]}"
                for lem in "${LEMMAS[@]}"; do
                    lem="${lem#"${lem%%[! ]*}"}"  # ltrim
                    lem="${lem%"${lem##*[! ]}"}"  # rtrim
                    [[ -n "$lem" ]] && LEMMA_SET["$lem"]=1
                done
            fi
        done
        if [[ -n "$BASE_CMD" && ${#LEMMA_SET[@]} -gt 0 ]]; then
            MERGED=$(IFS=', '; echo "${!LEMMA_SET[*]}")
            REPLACEMENT="${INDENT}${PREFIX}${BASE_CMD} [${MERGED}]${AT_TARGET}"
            RESULT_LINES[$IDX]="$REPLACEMENT"
            (( APPLIED_COUNT++ ))
        fi
        unset LEMMA_SET
    else
        # 単一提案
        SUGG="${SUGG_LIST[0]}"
        [[ -z "$SUGG" ]] && continue

        # at ターゲットが提案に含まれていなければ追加
        if [[ -n "$AT_TARGET" ]] && ! echo "$SUGG" | grep -qE '\bat\s'; then
            SUGG="${SUGG}${AT_TARGET}"
        fi

        RESULT_LINES[$IDX]="${INDENT}${PREFIX}${SUGG}"
        (( APPLIED_COUNT++ ))
    fi
done

info "適用: $APPLIED_COUNT 件, スキップ: $SKIPPED_COUNT 件"

# --- Step 6: 結果書き出し ---

{
    for (( i=0; i<${#RESULT_LINES[@]}; i++ )); do
        if (( i > 0 )); then printf '\n'; fi
        printf '%s' "${RESULT_LINES[$i]}"
    done
} > "$ABS_FILE"

ok "安定化完了: $APPLIED_COUNT / $CONVERT_COUNT 件"

# --- Step 7: クリーンアップ ---

if (( KEEP_BACKUP )); then
    info "バックアップ保持: $BAK_FILE"
    trap - EXIT  # cleanup をキャンセル
else
    rm -f "$BAK_FILE"
    info "バックアップ削除"
fi

info "次のステップ: lake build で検証してください"
info "unused simp argument 警告がある場合は手動で除去してください"
