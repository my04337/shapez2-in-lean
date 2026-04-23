#!/usr/bin/env bash
# SessionStart Hook: 証明状態の自動注入
# セッション開始時に docs/s2il/ と sorry 状況を収集し、
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

# --- セッション ID の生成 (.lake/session-id.tmp に書き込む) ---
LAKE_DIR="$CWD/.lake"
mkdir -p "$LAKE_DIR"
SESSION_ID_FILE="$LAKE_DIR/session-id.tmp"

# 8文字のランダム ID を生成（uuidgen があれば利用、なければ /dev/urandom）
if command -v uuidgen &>/dev/null; then
    SID=$(uuidgen | tr -d '-' | head -c 8 | tr '[:upper:]' '[:lower:]')
else
    SID=$(cat /dev/urandom | tr -dc 'a-z0-9' | head -c 8 2>/dev/null || echo "00000000")
fi
echo -n "$SID" > "$SESSION_ID_FILE"

# 前セッションのセッション固有診断ファイルを削除（クリーンアップ）
if [ -d "$LAKE_DIR" ]; then
    find "$LAKE_DIR" -maxdepth 1 -name 'build-diagnostics-*.jsonl' -delete 2>/dev/null || true
fi

MESSAGES=""

# --- 0. .gitignore の主要除外パスを通知 ---
GITIGNORE_FILE="$CWD/.gitignore"
if [ -f "$GITIGNORE_FILE" ]; then
    IGNORED_DIRS=$(grep -E '^\s*[^#].*/' "$GITIGNORE_FILE" | sed 's|/.*||; s/^[[:space:]]*//' | sort -u | tr '\n' ', ' | sed 's/, $//')
    if [ -n "$IGNORED_DIRS" ]; then
        MESSAGES="⚠ Gitignore excluded dirs: ${IGNORED_DIRS} — Files placed here are not tracked by git. Use Verification/ or similar for files that need to persist."
    fi
fi

# --- 1. docs/s2il/ から証明関連ファイルを収集 ---
KNOWLEDGE_DIR="$CWD/docs/s2il"
if [ -d "$KNOWLEDGE_DIR" ]; then
    PROOF_FILES=$(find "$KNOWLEDGE_DIR" -name "*.md" | grep -iE 'proof|sorry|settle|gravity|bfs|equivariance' || true)
    if [ -n "$PROOF_FILES" ]; then
        MESSAGES="Proof-related knowledge files:"
        while IFS= read -r f; do
            REL=$(echo "$f" | sed "s|$CWD/||")
            MESSAGES="$MESSAGES\n  - $REL"
        done <<< "$PROOF_FILES"
    fi
fi

# --- 2. .lean ファイル内の sorry 一覧（高速パス: build-diagnostics.jsonl → フォールバック: ファイルスキャン） ---
SORRY_INFO=""
TOTAL_SORRIES=0

DIAG_FILE="$CWD/.lake/build-diagnostics.jsonl"

if [ -f "$DIAG_FILE" ] && command -v jq &>/dev/null; then
    # 高速パス: 前回ビルドの診断結果から sorry を抽出
    while IFS= read -r line; do
        FILE=$(echo "$line" | cut -d' ' -f1)
        COUNT=$(echo "$line" | cut -d' ' -f2)
        SORRY_INFO="${SORRY_INFO}\n  - ${FILE}: ${COUNT} 件"
        TOTAL_SORRIES=$((TOTAL_SORRIES + COUNT))
    done < <(jq -r 'select(.isSorry == true) | .file' "$DIAG_FILE" 2>/dev/null | sort | uniq -c | awk '{print $2, $1}')
else
    # フォールバック: ファイルスキャン
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
                    SORRY_INFO="${SORRY_INFO}\n  - ${REL}: ${COUNT}"
                    TOTAL_SORRIES=$((TOTAL_SORRIES + COUNT))
                fi
            done < <(find "$DIR_PATH" -name "*.lean" 2>/dev/null)
        fi
    done
fi

if [ "$TOTAL_SORRIES" -gt 0 ]; then
    MESSAGES="${MESSAGES}\n\nCurrent sorry status (total: ${TOTAL_SORRIES}):${SORRY_INFO}"
fi

# --- 出力 ---
if [ -n "$MESSAGES" ]; then
    # JSON エスケープ（改行 → \n）
    ESCAPED=$(echo -e "$MESSAGES" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' '\\' | sed 's/\\/\\n/g; s/\\n$//')
    echo "{\"systemMessage\":\"[SessionStart] Project proof status:\\n${ESCAPED}\"}"
else
    echo "{\"systemMessage\":\"[SessionStart] No sorrys detected.\"}"
fi

exit 0
