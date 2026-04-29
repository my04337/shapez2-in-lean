#!/usr/bin/env bash
# PreCompact Hook: コンテキスト圧縮前のセッションメモリ保存促進
# コンテキスト圧縮（context compaction）が発生する直前に呼ばれ、
# エージェントに未保存の作業状態をセッションメモリに退避するよう促す。
#
# 入力 (stdin JSON): { "hookEventName": "PreCompact", "cwd": "...", ... }
# 出力 (stdout JSON): { "systemMessage": "..." }

set -euo pipefail

RAW_INPUT=$(cat)
CWD=$(echo "$RAW_INPUT" | python3 -c "import sys,json; print(json.load(sys.stdin).get('cwd','.'))" 2>/dev/null || echo ".")

MSG="Save current focus to /memories/session/ (target file:line + next 1–3 actions + sorry/error counts), then resume the next task. Use str_replace/insert to update existing memory; create only if no session memory exists yet."

# sorry 残数の補足情報（セッション固有診断ファイルを優先）
DIAG_FILE="$CWD/.lake/build-diagnostics.jsonl"
SESSION_ID_FILE="$CWD/.lake/session-id.tmp"
if [ -f "$SESSION_ID_FILE" ]; then
    PSID=$(cat "$SESSION_ID_FILE" | tr -d '[:space:]')
    if [ -n "$PSID" ]; then
        CANDIDATE="$CWD/.lake/build-diagnostics-$PSID.jsonl"
        if [ -f "$CANDIDATE" ]; then
            DIAG_FILE="$CANDIDATE"
        fi
    fi
fi
if [ -f "$DIAG_FILE" ]; then
    SORRY_COUNT=$(grep -c '"isSorry":true' "$DIAG_FILE" 2>/dev/null || echo "0")
    if [ "$SORRY_COUNT" -gt 0 ]; then
        MSG="$MSG Current sorry count (last build): ${SORRY_COUNT}."
    fi
fi

printf '{"systemMessage":"[PreCompact] %s"}' "$(echo -e "$MSG" | sed 's/"/\\"/g' | tr '\n' ' ')"
exit 0
