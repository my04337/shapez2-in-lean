#!/usr/bin/env bash
# lean-run: Lean プロジェクトのビルド・実行・出力検証 (bash/zsh)
# 使い方: ./run.sh [--target <name>] [--expected <string>]
set -euo pipefail

TARGET="s2il"
EXPECTED=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --target)   TARGET="$2"; shift 2 ;;
        --expected) EXPECTED="$2"; shift 2 ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# lean-build: ビルド (PATH 解決含む)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUILD_SCRIPT="$SCRIPT_DIR/../../lean-build/scripts/build.sh"
if [ -f "$BUILD_SCRIPT" ]; then
    bash "$BUILD_SCRIPT" --target "$TARGET"
else
    echo "==> lake build $TARGET"
    lake build "$TARGET"
fi

# 実行
echo "==> lake exe $TARGET"
output=$(lake exe "$TARGET")
echo "$output"

# 出力検証 (期待値が指定された場合)
if [ -n "$EXPECTED" ]; then
    if [ "$output" = "$EXPECTED" ]; then
        echo "検証OK: 出力が期待値と一致"
    else
        echo "検証NG: 期待='$EXPECTED' 実際='$output'" >&2
        exit 1
    fi
fi
