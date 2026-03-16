#!/usr/bin/env bash
# lean-build: Lean プロジェクトのビルド (bash/zsh)
# 使い方: ./build.sh [--clean] [--update] [--target <name>]
set -euo pipefail

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

# ビルド
if [ -n "$TARGET" ]; then
    echo "==> lake build $TARGET"
    lake build "$TARGET"
else
    echo "==> lake build"
    lake build
fi

echo "ビルド完了"
