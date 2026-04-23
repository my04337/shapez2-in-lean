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

# NOTE: jq は tool_input.content / newString / oldString 等に不正な JSON エスケープが
# 含まれる場合に失敗する場合があるため、フォールバックとして正規表現で抽出する。

# ファイルパスの取得
FILE_PATH=""
if command -v jq &>/dev/null; then
    FILE_PATH=$(echo "$INPUT_JSON" | jq -r '.tool_input.filePath // (.tool_input.replacements[0].filePath // "")' 2>/dev/null || echo "")
fi
# jq が失敗または不在の場合は grep/sed でフォールバック
if [[ -z "$FILE_PATH" ]]; then
    FILE_PATH=$(echo "$INPUT_JSON" | grep -o '"filePath"[[:space:]]*:[[:space:]]*"[^"]*"' | head -1 | sed 's/.*: *"//;s/"$//' || echo "")
fi

# .lean ファイルでなければスキップ
if [[ "$FILE_PATH" != *.lean ]] || [[ ! -f "$FILE_PATH" ]]; then
    echo '{}'
    exit 0
fi

# proof-suppressed.flag が存在する場合は証明フック出力を抑止する
CWD_FOR_FLAG=""
if command -v jq &>/dev/null; then
    CWD_FOR_FLAG=$(echo "$INPUT_JSON" | jq -r '.cwd // ""' 2>/dev/null || echo "")
fi
if [ -z "$CWD_FOR_FLAG" ]; then CWD_FOR_FLAG="$(pwd)"; fi
if [ -f "$CWD_FOR_FLAG/.lake/proof-suppressed.flag" ]; then
    echo '{}'
    exit 0
fi

# .lean ファイルが編集されたことをフラグで記録（Stop フックが sorry 通知要否を判断するために使用）
if [ -d "$CWD_FOR_FLAG/.lake" ]; then
    touch "$CWD_FOR_FLAG/.lake/lean-edited-this-turn.flag"
fi

# sorry カウント（コメント行を除外）
COUNT=$(grep -c '\bsorry\b' "$FILE_PATH" 2>/dev/null | head -1 || echo "0")
# コメント行の sorry を引く
COMMENT_COUNT=$(grep '^\s*--.*\bsorry\b' "$FILE_PATH" 2>/dev/null | wc -l || echo "0")
COUNT=$((COUNT - COMMENT_COUNT))

if [ "$COUNT" -gt 0 ]; then
    FILENAME=$(basename "$FILE_PATH")
    echo "{\"systemMessage\":\"[Hook] ${FILENAME}: ${COUNT} sorry(s). Please work toward completing the proofs.\"}"
else
    echo '{}'
fi

exit 0
