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

# proof-suppressed.flag が存在する場合は全証明フック出力を抑止する
# (session-efficiency スキル発動時やユーザが明示的に証明停止を指示した場合に作成される)
if [ -f "$CWD/.lake/proof-suppressed.flag" ]; then
    echo '{"continue":true}'
    exit 0
fi

# ======================================================================
# 0. セッション内にビルドが実行されたかチェック（Q&A セッション等の誤ブロック防止）
#    - .lake/session-id.tmp が存在 → セッションIDを取得
#    - .lake/build-diagnostics-<sid>.jsonl が存在 → このセッションでビルドあり
#    - どちらかが存在しない → このセッションではビルドしていない → スキップ
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
    # セッション内ビルドなし → スキップ（前セッション以前の診断を読まない）
    echo '{"continue":true}'
    exit 0
fi

# ======================================================================
# 1. build-diagnostics-<sid>.jsonl から非 sorry warning を検出してブロック判定
# ======================================================================
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
        REASON=$(printf '[Stop Hook] %d unresolved warning(s) found in the last build.\nWarnings originating from sorry have been excluded.\nPlease resolve the following warnings before exiting.\n\n%s' \
            "$NON_SORRY_COUNT" "$(printf '%b' "$NON_SORRY_LIST")")
        REASON_JSON=$(printf '%s' "$REASON" | jq -Rs .)
        echo "{\"hookSpecificOutput\":{\"hookEventName\":\"Stop\",\"decision\":\"block\",\"reason\":${REASON_JSON}}}"
    else
        echo "{\"hookSpecificOutput\":{\"hookEventName\":\"Stop\",\"decision\":\"block\",\"reason\":\"${NON_SORRY_COUNT} warning(s) unresolved (sorry-originating excluded)\"}}"
    fi
    exit 0
fi

# ======================================================================
# ======================================================================
# 2. untracked ファイルの警告（意図しない新規ファイルの検出）
# ======================================================================
UNTRACKED_WARNINGS=""
UNTRACKED_COUNT=0

if command -v git &>/dev/null; then
    cd "$CWD"
    while IFS= read -r line; do
        # "?? filename" から filename を抽出
        FILE=$(echo "$line" | sed 's/^?? //' | tr -d '"')
        # トップレベルの .lean/.md ファイルのみ対象
        if echo "$FILE" | grep -qvE '/' && echo "$FILE" | grep -qE '\.(lean|md)$'; then
            UNTRACKED_WARNINGS="${UNTRACKED_WARNINGS}  - ${FILE}\n"
            UNTRACKED_COUNT=$((UNTRACKED_COUNT + 1))
        fi
    done < <(git status --porcelain 2>/dev/null | grep '^??')
fi

if [ "$UNTRACKED_COUNT" -gt 0 ]; then
    if command -v jq &>/dev/null; then
        REASON=$(printf '[Stop Hook] %d unexpected untracked file(s) found in the project root.\nPlace temporary files in Scratch/ or delete them if unnecessary.\n\n%s' \
            "$UNTRACKED_COUNT" "$(printf '%b' "$UNTRACKED_WARNINGS")")
        REASON_JSON=$(printf '%s' "$REASON" | jq -Rs .)
        echo "{\"hookSpecificOutput\":{\"hookEventName\":\"Stop\",\"decision\":\"block\",\"reason\":${REASON_JSON}}}"
    else
        echo "{\"hookSpecificOutput\":{\"hookEventName\":\"Stop\",\"decision\":\"block\",\"reason\":\"${UNTRACKED_COUNT} untracked file(s) in the project root\"}}"
    fi
    exit 0
fi

# ======================================================================
# 3. sorry の残存チェック (情報通知のみ、ブロックしない)
#    ターン内に .lean ファイル編集があった場合のみ通知する
#    build 診断の isSorry=true を唯一の情報源とする
# ======================================================================
# .lean 編集フラグの確認とリセット
LEAN_EDITED_FLAG="$CWD/.lake/lean-edited-this-turn.flag"
LEAN_WAS_EDITED="false"
if [ -f "$LEAN_EDITED_FLAG" ]; then
    LEAN_WAS_EDITED="true"
    rm -f "$LEAN_EDITED_FLAG"
fi
SORRY_INFO=""
TOTAL_SORRIES=0

if [ -f "$DIAG_FILE" ] && command -v jq &>/dev/null; then
    while IFS= read -r line; do
        [ -z "$line" ] && continue
        FILE=$(echo "$line" | jq -r '.file // ""' 2>/dev/null || echo "")
        COUNT=$(echo "$line" | jq -r '.count // 0' 2>/dev/null || echo "0")
        [ -z "$FILE" ] && continue
        SORRY_INFO="${SORRY_INFO}  - ${FILE}: ${COUNT}\n"
        TOTAL_SORRIES=$((TOTAL_SORRIES + COUNT))
    done < <(jq -sc 'map(select(.isSorry == true)) | group_by(.file)[] | { file: .[0].file, count: length }' "$DIAG_FILE" 2>/dev/null)
fi

if [ "$TOTAL_SORRIES" -gt 0 ]; then
    if [ "$LEAN_WAS_EDITED" = "true" ]; then
        MSG="[Stop] ${TOTAL_SORRIES} sorry(s) remain. Recommended: record proof progress in /memories/repo/ before ending the session.\\n\\nRemaining sorrys:\\n${SORRY_INFO}"
        echo "{\"continue\":true,\"systemMessage\":\"${MSG}\"}"
    else
        # .lean 編集なしターン: sorry 実証作業を行っていないため通知を抑止する
        echo '{"continue":true}'
    fi
else
    echo '{"continue":true}'
fi

exit 0
