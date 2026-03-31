#!/usr/bin/env bash
# lean-depgraph: 証明依存グラフの生成 (Bash)
# 使い方: ./depgraph.sh [--private] [--json] [--ns <name>] [--theorems-only] [--output <path>]
#                  [--root <name>] [--root-reverse]
#
# 出力:
#   指定パスまたは .lake/depgraph.md (.json) - グラフ本体
#   stdout - 構造化サマリー (=== DEPGRAPH RESULT === ... === END DEPGRAPH ===)

set -euo pipefail

# --- 引数解析 ---
PRIVATE=""
JSON=""
NAMESPACE=""
THEOREMS_ONLY=""
OUTPUT=""
ROOT=""
ROOT_REVERSE=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --private) PRIVATE="--private"; shift ;;
        --json) JSON="--json"; shift ;;
        --ns) NAMESPACE="$2"; shift 2 ;;
        --theorems-only) THEOREMS_ONLY="--theorems-only"; shift ;;
        --output) OUTPUT="$2"; shift 2 ;;
        --root) ROOT="$2"; shift 2 ;;
        --root-reverse) ROOT_REVERSE="--root-reverse"; shift ;;
        *) shift ;;
    esac
done

# lean-setup: PATH 解決
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SETUP_SCRIPT="$SCRIPT_DIR/../../lean-setup/scripts/setup.sh"
if [[ -f "$SETUP_SCRIPT" ]]; then
    # shellcheck source=/dev/null
    source "$SETUP_SCRIPT"
fi

# depgraph ターゲットのビルド（S2IL も自動でビルドされる）
echo "==> lake build depgraph --no-ansi"
if ! lake build depgraph --no-ansi; then
    echo ""
    echo "=== DEPGRAPH RESULT ==="
    echo "status: failed"
    echo "reason: build_failed"
    echo "=== END DEPGRAPH ==="
    exit 1
fi

# .lake ディレクトリの確保
PROJECT_ROOT="$SCRIPT_DIR/../../../.."
LAKE_DIR="$(cd "$PROJECT_ROOT" && pwd)/.lake"
mkdir -p "$LAKE_DIR"

# 出力先の決定
if [[ -n "$OUTPUT" ]]; then
    OUTPUT_PATH="$OUTPUT"
elif [[ -n "$JSON" ]]; then
    OUTPUT_PATH="$LAKE_DIR/depgraph.json"
else
    OUTPUT_PATH="$LAKE_DIR/depgraph.md"
fi

# lake exe 引数の組み立て
DEP_ARGS=()
[[ -n "$PRIVATE" ]] && DEP_ARGS+=("--private")
[[ -n "$JSON" ]] && DEP_ARGS+=("--json")
[[ -n "$NAMESPACE" ]] && DEP_ARGS+=("--ns" "$NAMESPACE")
[[ -n "$THEOREMS_ONLY" ]] && DEP_ARGS+=("--theorems-only")
[[ -n "$ROOT" ]] && DEP_ARGS+=("--root" "$ROOT")
[[ -n "$ROOT_REVERSE" ]] && DEP_ARGS+=("--root-reverse")
DEP_ARGS+=("--output" "$OUTPUT_PATH")

# 実行
echo "==> lake exe depgraph ${DEP_ARGS[*]}"
RUN_OUTPUT=$(lake exe depgraph "${DEP_ARGS[@]}" 2>&1) || RUN_EXIT=$?
RUN_EXIT=${RUN_EXIT:-0}

# --- 結果サマリー ---
echo ""
echo "=== DEPGRAPH RESULT ==="

if [[ "$RUN_EXIT" -eq 0 ]]; then
    echo "status: success"
else
    echo "status: failed"
fi
echo "exit_code: $RUN_EXIT"
echo "output: $OUTPUT_PATH"

# 統計情報の表示
IN_STATS=false
while IFS= read -r line; do
    if [[ "$line" == *"=== DEPGRAPH STATISTICS ==="* ]]; then IN_STATS=true; fi
    if $IN_STATS; then echo "$line"; fi
    if [[ "$line" == *"=== END STATISTICS ==="* ]]; then IN_STATS=false; fi
done <<< "$RUN_OUTPUT"

echo "=== END DEPGRAPH ==="

exit "$RUN_EXIT"
