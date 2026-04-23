#!/usr/bin/env bash
# Stop Hook: セッション終了時のインデックス自動再生成（M7）
#
# S2IL のビルドが成功している場合に限り、以下のインデックスを自動再生成する:
#   - S2IL/_agent/symbol-map.jsonl（シンボル位置 DB）
#   - S2IL/_agent/dep-graph-baseline.json（依存グラフベースライン）
#
# 入力 (stdin JSON): { "hookEventName": "Stop", "cwd": "...", ... }
# 出力 (stdout JSON): { "continue": true } or { "continue": true, "systemMessage": "..." }

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

if [ "$STOP_ACTIVE" = "true" ]; then
    echo '{"continue":true}'
    exit 0
fi

if [ -z "$CWD" ]; then
    CWD="$(pwd)"
fi

cd "$CWD"

# ======================================================================
# 0. ビルド成功チェック
# ======================================================================
SESSION_ID_FILE="$CWD/.lake/session-id.tmp"
DIAG_FILE=""

if [ -f "$SESSION_ID_FILE" ]; then
    SID=$(cat "$SESSION_ID_FILE" | tr -d '[:space:]')
    if [ -n "$SID" ]; then
        CANDIDATE="$CWD/.lake/build-diagnostics-$SID.jsonl"
        if [ -f "$CANDIDATE" ]; then
            DIAG_FILE="$CANDIDATE"
        fi
    fi
fi

if [ -z "$DIAG_FILE" ]; then
    echo '{"continue":true}'
    exit 0
fi

# エラーがあればスキップ
if command -v jq &>/dev/null; then
    ERROR_COUNT=$(jq -s 'map(select(.severity == "error")) | length' "$DIAG_FILE" 2>/dev/null || echo "0")
else
    ERROR_COUNT=$(grep -c '"error"' "$DIAG_FILE" 2>/dev/null || echo "0")
fi

if [ "$ERROR_COUNT" -gt 0 ]; then
    echo '{"continue":true}'
    exit 0
fi

# ======================================================================
# 1. .lean ファイルの変更検出
# ======================================================================
LEAN_CHANGED=false
if command -v git &>/dev/null; then
    DIFF_COUNT=$( (git diff --name-only HEAD 2>/dev/null; git diff --name-only --cached 2>/dev/null; git ls-files --others --exclude-standard '*.lean' 2>/dev/null) | grep '\.lean$' | wc -l)
    if [ "$DIFF_COUNT" -gt 0 ]; then
        LEAN_CHANGED=true
    fi
fi

if [ "$LEAN_CHANGED" = "false" ]; then
    echo '{"continue":true}'
    exit 0
fi

# ======================================================================
# 2. インデックス再生成
# ======================================================================
# elan PATH
export PATH="$HOME/.elan/bin:$PATH"

REGENERATED=""
ERRORS=""

SYMBOL_MAP="$CWD/S2IL/_agent/symbol-map.jsonl"
DEP_GRAPH="$CWD/S2IL/_agent/dep-graph-baseline.json"

# symbol-map.jsonl
if lake exe s2il-toolkit symbol-map --output "$SYMBOL_MAP" 2>/dev/null; then
    REGENERATED="symbol-map.jsonl"
else
    ERRORS="symbol-map: exit $?"
fi

# dep-graph-baseline.json
if lake exe s2il-toolkit depgraph --json --output "$DEP_GRAPH" 2>/dev/null; then
    if [ -n "$REGENERATED" ]; then
        REGENERATED="$REGENERATED, dep-graph-baseline.json"
    else
        REGENERATED="dep-graph-baseline.json"
    fi
else
    ERR="dep-graph: exit $?"
    if [ -n "$ERRORS" ]; then
        ERRORS="$ERRORS; $ERR"
    else
        ERRORS="$ERR"
    fi
fi

# ======================================================================
# 3. git add
# ======================================================================
if [ -n "$REGENERATED" ]; then
    git add "$SYMBOL_MAP" "$DEP_GRAPH" 2>/dev/null || true
fi

# ======================================================================
# 4. 結果通知
# ======================================================================
MSG=""
if [ -n "$REGENERATED" ]; then
    MSG="[M7] Regenerated: $REGENERATED"
fi
if [ -n "$ERRORS" ]; then
    if [ -n "$MSG" ]; then
        MSG="$MSG\n[M7] Failed: $ERRORS"
    else
        MSG="[M7] Failed: $ERRORS"
    fi
fi

if [ -n "$MSG" ]; then
    if command -v jq &>/dev/null; then
        MSG_JSON=$(printf '%s' "$MSG" | jq -Rs .)
        echo "{\"continue\":true,\"systemMessage\":${MSG_JSON}}"
    else
        echo "{\"continue\":true,\"systemMessage\":\"$MSG\"}"
    fi
else
    echo '{"continue":true}'
fi

exit 0
