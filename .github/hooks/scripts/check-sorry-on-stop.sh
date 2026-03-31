#!/usr/bin/env bash
# Stop Hook: セッション終了前の warning チェック
# 非 sorry warning が残っている場合はエージェントをブロックする。
# sorry に起因する warning はブロック対象外とし、進捗記録を促すのみとする。
#
# 入力 (stdin JSON): { "hookEventName": "Stop", "cwd": "...", "stop_hook_active": false, ... }
# 出力 (stdout JSON):
#   ブロック時: { "hookSpecificOutput": { "hookEventName": "Stop", "decision": "block", "reason": "..." } }
#   通過時:     { "continue": true } または { "continue": true, "systemMessage": "..." }

set -euo pipefail

INPUT_JSON=$(cat)

# cwd・stop_active の取得
CWD=""
STOP_ACTIVE="false"
if command -v jq &>/dev/null; then
    CWD=$(echo "$INPUT_JSON" | jq -r '.cwd // ""')
    STOP_ACTIVE=$(echo "$INPUT_JSON" | jq -r '.stop_hook_active // false')
else
    CWD="$(pwd)"
fi

# 無限ループ防止
if [ "$STOP_ACTIVE" = "true" ]; then
    echo '{"continue":true}'
    exit 0
fi

if [ -z "$CWD" ]; then
    CWD="$(pwd)"
fi

# ======================================================================
# 1. build-diagnostics.jsonl から非 sorry warning を検出してブロック判定
# ======================================================================
DIAG_FILE="$CWD/.lake/build-diagnostics.jsonl"
NON_SORRY_COUNT=0
NON_SORRY_LIST=""

if [ -f "$DIAG_FILE" ]; then
    if command -v jq &>/dev/null; then
        # jq が利用可能: 正確なフィルタリング
        while IFS= read -r line; do
            [ -z "$line" ] && continue
            SEVERITY=$(echo "$line" | jq -r '.severity // ""' 2>/dev/null || echo "")
            IS_SORRY=$(echo "$line" | jq -r '.isSorry // false' 2>/dev/null || echo "false")
            if [ "$SEVERITY" = "warning" ] && [ "$IS_SORRY" != "true" ]; then
                F=$(echo "$line" | jq -r '.file // ""')
                L=$(echo "$line" | jq -r '.line // ""')
                C=$(echo "$line" | jq -r '.col // ""')
                M=$(echo "$line" | jq -r '.message // ""')
                NON_SORRY_LIST="${NON_SORRY_LIST}  [${F}:${L}:${C}] ${M}\n"
                NON_SORRY_COUNT=$((NON_SORRY_COUNT + 1))
            fi
        done < "$DIAG_FILE"
    else
        # jq なし: grep による近似カウント
        WARN_COUNT=$(grep -c '"warning"' "$DIAG_FILE" 2>/dev/null || echo "0")
        SORRY_COUNT=$(grep -c '"isSorry":true' "$DIAG_FILE" 2>/dev/null || echo "0")
        NON_SORRY_COUNT=$((WARN_COUNT - SORRY_COUNT))
        [ "$NON_SORRY_COUNT" -lt 0 ] && NON_SORRY_COUNT=0
    fi
fi

if [ "$NON_SORRY_COUNT" -gt 0 ]; then
    if command -v jq &>/dev/null; then
        REASON=$(printf '[Stop Hook] 前回ビルドで未解消の warning が %d 件あります。\nsorry に起因する warning は除外済みです。\n以下の warning を解消してから終了してください。\n\n%s' \
            "$NON_SORRY_COUNT" "$(printf '%b' "$NON_SORRY_LIST")")
        REASON_JSON=$(printf '%s' "$REASON" | jq -Rs .)
        echo "{\"hookSpecificOutput\":{\"hookEventName\":\"Stop\",\"decision\":\"block\",\"reason\":${REASON_JSON}}}"
    else
        echo "{\"hookSpecificOutput\":{\"hookEventName\":\"Stop\",\"decision\":\"block\",\"reason\":\"warning ${NON_SORRY_COUNT} 件未解消 (sorry 由来除外済み)\"}}"
    fi
    exit 0
fi

# ======================================================================
# 2. sorry の残存チェック (情報通知のみ、ブロックしない)
# ======================================================================
SORRY_INFO=""
TOTAL_SORRIES=0

DIR_PATH="$CWD/S2IL"
if [ -d "$DIR_PATH" ]; then
    while IFS= read -r f; do
        COUNT=$(grep -c '\bsorry\b' "$f" 2>/dev/null || echo "0")
        COMMENT_COUNT=$(grep -c '^\s*--.*\bsorry\b' "$f" 2>/dev/null || echo "0")
        COUNT=$((COUNT - COMMENT_COUNT))
        if [ "$COUNT" -gt 0 ]; then
            REL=$(echo "$f" | sed "s|$CWD/||")
            SORRY_INFO="${SORRY_INFO}  - ${REL}: ${COUNT} 件\n"
            TOTAL_SORRIES=$((TOTAL_SORRIES + COUNT))
        fi
    done < <(find "$DIR_PATH" -name "*.lean" 2>/dev/null)
fi

if [ "$TOTAL_SORRIES" -gt 0 ]; then
    MSG="[Stop] sorry が ${TOTAL_SORRIES} 件残っています。セッション終了前に、証明の進捗状態をリポジトリメモリ (/memories/repo/) に記録することを推奨します。\\n\\n残存 sorry:\\n${SORRY_INFO}"
    echo "{\"continue\":true,\"systemMessage\":\"${MSG}\"}"
else
    echo '{"continue":true}'
fi

exit 0
