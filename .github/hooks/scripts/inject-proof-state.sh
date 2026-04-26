#!/usr/bin/env bash
# SessionStart Hook: コンテキスト注入の最小化
# セッション開始時にセッション情報と最小限の補助メッセージを注入する
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

# --- 出力 ---
if [ -n "$MESSAGES" ]; then
    # JSON エスケープ（改行 → \n）
    ESCAPED=$(echo -e "$MESSAGES" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' '\\' | sed 's/\\/\\n/g; s/\\n$//')
    echo "{\"systemMessage\":\"[SessionStart] Session ID: ${SID} (REPL JSONL template: Scratch/commands-${SID}-<topic>-<runId>.jsonl; use unique runId for parallel runs)\\n${ESCAPED}\"}"
else
    echo "{\"systemMessage\":\"[SessionStart] Session ID: ${SID} (REPL JSONL template: Scratch/commands-${SID}-<topic>-<runId>.jsonl; use unique runId for parallel runs)\"}"
fi

exit 0
