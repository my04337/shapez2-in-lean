#!/usr/bin/env bash
# Stop Hook: セッション終了前の sorry 残存チェック
# sorry が残っている場合に警告メッセージを出し、進捗記録を促す
#
# 入力 (stdin JSON): { "hookEventName": "Stop", "cwd": "...", "stop_hook_active": false, ... }
# 出力 (stdout JSON): { "systemMessage": "...", "continue": true }

set -euo pipefail

INPUT_JSON=$(cat)

# cwd の取得
CWD=""
if command -v jq &>/dev/null; then
    CWD=$(echo "$INPUT_JSON" | jq -r '.cwd // ""')
    STOP_ACTIVE=$(echo "$INPUT_JSON" | jq -r '.stop_hook_active // false')
else
    CWD="$(pwd)"
    STOP_ACTIVE="false"
fi

# 無限ループ防止
if [ "$STOP_ACTIVE" = "true" ]; then
    echo '{"continue":true}'
    exit 0
fi

if [ -z "$CWD" ]; then
    CWD="$(pwd)"
fi

# .lean ファイルの sorry を高速スキャン
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
