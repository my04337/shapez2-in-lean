#!/usr/bin/env bash
# PostToolUse Hook: .lean ファイル編集後の sorry カウント
# stdin から JSON を読み、対象ファイルが .lean の場合に sorry 数を systemMessage として返す
#
# 入力 (stdin JSON): { "tool_name": "...", "tool_input": { "filePath": "..." }, ... }
# 出力 (stdout JSON): { "systemMessage": "..." } or {}

set -euo pipefail

INPUT_JSON=$(cat)

# ツール名の取得
TOOL_NAME=$(echo "$INPUT_JSON" | grep -o '"tool_name"\s*:\s*"[^"]*"' | head -1 | sed 's/.*: *"//;s/"$//')

# 編集ツール以外はスキップ
case "$TOOL_NAME" in
    replace_string_in_file|multi_replace_string_in_file|create_file)
        ;;
    *)
        echo '{}'
        exit 0
        ;;
esac

# ファイルパスの取得（jq が利用可能ならそちらを優先）
FILE_PATH=""
if command -v jq &>/dev/null; then
    FILE_PATH=$(echo "$INPUT_JSON" | jq -r '.tool_input.filePath // (.tool_input.replacements[0].filePath // "")')
else
    FILE_PATH=$(echo "$INPUT_JSON" | grep -o '"filePath"\s*:\s*"[^"]*"' | head -1 | sed 's/.*: *"//;s/"$//')
fi

# .lean ファイルでなければスキップ
if [[ "$FILE_PATH" != *.lean ]] || [[ ! -f "$FILE_PATH" ]]; then
    echo '{}'
    exit 0
fi

# sorry カウント（コメント行を除外）
COUNT=$(grep -c '\bsorry\b' "$FILE_PATH" 2>/dev/null | head -1 || echo "0")
# コメント行の sorry を引く
COMMENT_COUNT=$(grep '^\s*--.*\bsorry\b' "$FILE_PATH" 2>/dev/null | wc -l || echo "0")
COUNT=$((COUNT - COMMENT_COUNT))

if [ "$COUNT" -gt 0 ]; then
    FILENAME=$(basename "$FILE_PATH")
    echo "{\"systemMessage\":\"[Hook] ${FILENAME} の sorry 数: ${COUNT} 件。証明の完了を目指してください。\"}"
else
    echo '{}'
fi

exit 0
