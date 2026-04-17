#!/usr/bin/env bash
# lean-build: Lean プロジェクトのビルド (bash/zsh)
# 使い方: ./build.sh [--clean] [--update] [--target <name>]
#
# 出力:
#   stdout  - 構造化サマリー (=== BUILD DIAGNOSTICS === ... === END DIAGNOSTICS ===)
#   .lake/build-log.txt          - 全ビルドログ
#   .lake/build-diagnostics.jsonl - 診断メッセージ (1行1JSON)
set -uo pipefail

CLEAN=false
UPDATE=false
TARGET=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --clean)  CLEAN=true; shift ;;
        --update) UPDATE=true; shift ;;
        --target) TARGET="$2"; shift 2 ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# lean-setup: PATH 解決
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SETUP_SCRIPT="$SCRIPT_DIR/../../lean-setup/scripts/setup.sh"
if [ -f "$SETUP_SCRIPT" ]; then
    # shellcheck source=../../lean-setup/scripts/setup.sh
    source "$SETUP_SCRIPT"
fi

# クリーンビルド
if [ "$CLEAN" = true ]; then
    echo "==> lake clean"
    lake clean
fi

# 依存更新
if [ "$UPDATE" = true ]; then
    echo "==> lake update"
    lake update
fi

# --- ビルド実行 & ログキャプチャ ---
BUILD_ARGS="build --no-ansi"
if [ -n "$TARGET" ]; then
    BUILD_ARGS="$BUILD_ARGS $TARGET"
fi

echo "==> lake $BUILD_ARGS"

# .lake ディレクトリの確保
LAKE_DIR="$(cd "$SCRIPT_DIR/../../../.." && pwd)/.lake"
mkdir -p "$LAKE_DIR"

LOG_PATH="$LAKE_DIR/build-log.txt"
JSONL_PATH="$LAKE_DIR/build-diagnostics.jsonl"

# lake build を実行し、全出力をキャプチャ（終了コードを保持）
set +e
if [ -n "$TARGET" ]; then
    lake build --no-ansi "$TARGET" 2>&1 | tee "$LOG_PATH"
else
    lake build --no-ansi 2>&1 | tee "$LOG_PATH"
fi
BUILD_EXIT_CODE=${PIPESTATUS[0]}
set -e

# --- 診断メッセージのパース ---
ERROR_COUNT=0
WARNING_COUNT=0
SORRY_COUNT=0
INFO_COUNT=0

# セッション固有パスを決定
SESSION_ID_FILE="$LAKE_DIR/session-id.tmp"
SESSION_JSONL_PATH="$JSONL_PATH"  # デフォルトは固定名
if [ -f "$SESSION_ID_FILE" ]; then
    SID=$(cat "$SESSION_ID_FILE" | tr -d '[:space:]')
    if [ -n "$SID" ]; then
        SESSION_JSONL_PATH="$LAKE_DIR/build-diagnostics-$SID.jsonl"
    fi
fi

# JSONL ファイルを初期化
> "$SESSION_JSONL_PATH"

# 診断行を一時ファイルに分類
DIAG_ERRORS=""
DIAG_SORRIES=""
DIAG_WARNINGS=""
DIAG_INFOS=""

while IFS= read -r line; do
    # Lake 出力形式: "severity: file:line:col: message"
    if [[ "$line" =~ ^(error|warning|info):\ (.+):([0-9]+):([0-9]+):\ (.+)$ ]]; then
        d_severity="${BASH_REMATCH[1]}"
        d_file="${BASH_REMATCH[2]}"
        d_line="${BASH_REMATCH[3]}"
        d_col="${BASH_REMATCH[4]}"
        d_message="${BASH_REMATCH[5]}"

        # sorry 判定 (バッククォートまたはシングルクォート)
        is_sorry=false
        if [[ "$d_message" == *"declaration uses"*"sorry"* ]]; then
            is_sorry=true
        fi

        # JSON エスケープ（簡易: ダブルクォートとバックスラッシュ）
        d_message_escaped="${d_message//\\/\\\\}"
        d_message_escaped="${d_message_escaped//\"/\\\"}"

        echo "{\"file\":\"$d_file\",\"line\":$d_line,\"col\":$d_col,\"severity\":\"$d_severity\",\"message\":\"$d_message_escaped\",\"isSorry\":$is_sorry}" >> "$SESSION_JSONL_PATH"

        # カウントと分類
        case "$d_severity" in
            error)
                ERROR_COUNT=$((ERROR_COUNT + 1))
                DIAG_ERRORS="${DIAG_ERRORS}[ERROR] ${d_file}:${d_line}:${d_col}: ${d_message}"$'\n'
                ;;
            warning)
                if [ "$is_sorry" = true ]; then
                    SORRY_COUNT=$((SORRY_COUNT + 1))
                    DIAG_SORRIES="${DIAG_SORRIES}[SORRY] ${d_file}:${d_line}:${d_col}: ${d_message}"$'\n'
                else
                    WARNING_COUNT=$((WARNING_COUNT + 1))
                    DIAG_WARNINGS="${DIAG_WARNINGS}[WARNING] ${d_file}:${d_line}:${d_col}: ${d_message}"$'\n'
                fi
                ;;
            info)
                INFO_COUNT=$((INFO_COUNT + 1))
                DIAG_INFOS="${DIAG_INFOS}[INFO] ${d_file}:${d_line}:${d_col}: ${d_message}"$'\n'
                ;;
        esac
    fi
done < "$LOG_PATH"

if [ "$BUILD_EXIT_CODE" -eq 0 ]; then
    STATUS="success"
else
    STATUS="failure"
fi

# セッション固有ファイルを固定名にもコピー（下位互換）
if [ "$SESSION_JSONL_PATH" != "$JSONL_PATH" ]; then
    cp "$SESSION_JSONL_PATH" "$JSONL_PATH"
fi

# --- 構造化サマリー出力 ---
echo ""
echo "=== BUILD DIAGNOSTICS ==="
echo "status: $STATUS"
echo "exit_code: $BUILD_EXIT_CODE"
echo "errors: $ERROR_COUNT"
echo "sorries: $SORRY_COUNT"
echo "warnings: $WARNING_COUNT"
echo "info: $INFO_COUNT"
echo "log: $LOG_PATH"
echo "diagnostics: $SESSION_JSONL_PATH"
echo ""

# トリアージ順: error > sorry > warning > info (最大20件)
SHOWN=0
MAX_SHOW=20

print_diags() {
    local diags="$1"
    if [ -z "$diags" ]; then return; fi
    while IFS= read -r dline; do
        if [ -z "$dline" ]; then continue; fi
        if [ "$SHOWN" -ge "$MAX_SHOW" ]; then
            echo "... (以降省略、全件は $SESSION_JSONL_PATH を参照)"
            return
        fi
        echo "$dline"
        SHOWN=$((SHOWN + 1))
    done <<< "$diags"
}

print_diags "$DIAG_ERRORS"
print_diags "$DIAG_SORRIES"
print_diags "$DIAG_WARNINGS"
print_diags "$DIAG_INFOS"

echo "=== END DIAGNOSTICS ==="

# ビルド失敗時は非ゼロで終了
if [ "$BUILD_EXIT_CODE" -ne 0 ]; then
    exit "$BUILD_EXIT_CODE"
fi
