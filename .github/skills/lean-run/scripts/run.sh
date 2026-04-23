#!/usr/bin/env bash
# lean-run: Lean プロジェクトのビルド・実行・出力検証 (bash/zsh)
# 使い方: ./run.sh [--target <name>] [--expected <string>]
#
# 出力:
#   stdout  - ビルド診断サマリー + 実行結果サマリー
#   .lake/build-log.txt          - 全ビルドログ (build.sh が生成)
#   .lake/build-diagnostics.jsonl - ビルド診断 (build.sh が生成)
#   .lake/run-log.txt            - 実行ログ
set -uo pipefail

TARGET="s2il"
EXPECTED=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --target)   TARGET="$2"; shift 2 ;;
        --expected) EXPECTED="$2"; shift 2 ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# lean-build: 全デフォルトターゲットをビルド (PATH 解決含む)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUILD_SCRIPT="$SCRIPT_DIR/../../lean-build/scripts/build.sh"
BUILD_FAILED=false
if [ -f "$BUILD_SCRIPT" ]; then
    "$BUILD_SCRIPT" || BUILD_FAILED=true
else
    echo "==> lake build"
    lake build || BUILD_FAILED=true
fi

# ビルド失敗時は実行をスキップ
if [ "$BUILD_FAILED" = true ]; then
    echo ""
    echo "=== RUN RESULT ==="
    echo "status: skipped"
    echo "reason: build_failed"
    echo "=== END RUN ==="
    exit 1
fi

# --- 実行 ---
echo "==> lake exe $TARGET"

LAKE_DIR="$(cd "$SCRIPT_DIR/../../../.." && pwd)/.lake"
mkdir -p "$LAKE_DIR"
RUN_LOG_PATH="$LAKE_DIR/run-log.txt"

set +e
lake exe "$TARGET" 2>&1 | tee "$RUN_LOG_PATH"
RUN_EXIT_CODE=${PIPESTATUS[0]}
set -e

# --- 実行結果サマリー ---
if [ "$RUN_EXIT_CODE" -eq 0 ]; then
    RUN_STATUS="success"
else
    RUN_STATUS="failure"
fi

OUTPUT_LINES=$(wc -l < "$RUN_LOG_PATH" | tr -d ' ')

echo ""
echo "=== RUN RESULT ==="
echo "status: $RUN_STATUS"
echo "exit_code: $RUN_EXIT_CODE"
echo "target: $TARGET"
echo "log: $RUN_LOG_PATH"
echo "output_lines: $OUTPUT_LINES"

# 出力検証 (期待値が指定された場合)
if [ -n "$EXPECTED" ]; then
    ACTUAL=$(cat "$RUN_LOG_PATH" | tr -d '\r' | sed '/^$/d')
    if [ "$ACTUAL" = "$EXPECTED" ]; then
        echo "verification: pass"
    else
        echo "verification: fail"
        echo "expected: $EXPECTED"
        echo "actual: $ACTUAL"
    fi
fi

echo "=== END RUN ==="

# 実行失敗時は非ゼロで終了
if [ "$RUN_EXIT_CODE" -ne 0 ]; then
    exit "$RUN_EXIT_CODE"
fi
