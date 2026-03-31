#!/usr/bin/env bash
# SessionStart Hook: 証明状態の自動注入
# セッション開始時に docs/knowledge/ と sorry 状況を収集し、
# エージェントのコンテキストに注入する
#
# 入力 (stdin JSON): { "hookEventName": "SessionStart", "cwd": "...", ... }
# 出力 (stdout JSON): { "systemMessage": "..." }

set -euo pipefail

INPUT_JSON=$(cat)

# cwd の取得
CWD=""
if command -v jq &>/dev/null; then
    CWD=$(echo "$INPUT_JSON" | jq -r '.cwd // ""')
fi
if [ -z "$CWD" ]; then
    CWD="$(pwd)"
fi

MESSAGES=""

# --- 1. docs/knowledge/ から証明関連ファイルを収集 ---
KNOWLEDGE_DIR="$CWD/docs/knowledge"
if [ -d "$KNOWLEDGE_DIR" ]; then
    PROOF_FILES=$(find "$KNOWLEDGE_DIR" -name "*.md" | grep -iE 'proof|sorry|settle|gravity|bfs|equivariance' || true)
    if [ -n "$PROOF_FILES" ]; then
        MESSAGES="証明関連ナレッジファイル:"
        while IFS= read -r f; do
            REL=$(echo "$f" | sed "s|$CWD/||")
            MESSAGES="$MESSAGES\n  - $REL"
        done <<< "$PROOF_FILES"
    fi
fi

# --- 2. .lean ファイル内の sorry 一覧 ---
SORRY_INFO=""
TOTAL_SORRIES=0

for dir in S2IL Test; do
    DIR_PATH="$CWD/$dir"
    if [ -d "$DIR_PATH" ]; then
        while IFS= read -r f; do
            # コメント行を除外して sorry をカウント
            COUNT=$(grep -c '\bsorry\b' "$f" 2>/dev/null || echo "0")
            COMMENT_COUNT=$(grep -c '^\s*--.*\bsorry\b' "$f" 2>/dev/null || echo "0")
            COUNT=$((COUNT - COMMENT_COUNT))
            if [ "$COUNT" -gt 0 ]; then
                REL=$(echo "$f" | sed "s|$CWD/||")
                SORRY_INFO="${SORRY_INFO}\n  - ${REL}: ${COUNT} 件"
                TOTAL_SORRIES=$((TOTAL_SORRIES + COUNT))
            fi
        done < <(find "$DIR_PATH" -name "*.lean" 2>/dev/null)
    fi
done

if [ "$TOTAL_SORRIES" -gt 0 ]; then
    MESSAGES="${MESSAGES}\n\n現在の sorry 状況 (合計: ${TOTAL_SORRIES} 件):${SORRY_INFO}"
fi

# --- 出力 ---
if [ -n "$MESSAGES" ]; then
    # JSON エスケープ（改行 → \n）
    ESCAPED=$(echo -e "$MESSAGES" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' '\\' | sed 's/\\/\\n/g; s/\\n$//')
    echo "{\"systemMessage\":\"[SessionStart] プロジェクト証明状態:\\n${ESCAPED}\"}"
else
    echo "{\"systemMessage\":\"[SessionStart] sorry は検出されませんでした。\"}"
fi

exit 0
