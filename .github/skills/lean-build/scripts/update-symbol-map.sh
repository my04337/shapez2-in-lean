#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 my04337
# SPDX-License-Identifier: MIT
#
# update-symbol-map.sh — S2IL/_agent/symbol-map.jsonl を Lean ソースから再生成する
# lean-build/scripts/build.sh からビルド成功後に自動呼び出しされる。
#
# 使い方:
#   .github/skills/lean-build/scripts/update-symbol-map.sh [--root <workspace-root>]

set -euo pipefail

# --- 引数パース ---

ROOT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --root) ROOT="$2"; shift 2 ;;
        *) echo "[update-symbol-map] 不明なオプション: $1" >&2; exit 1 ;;
    esac
done

# --- ワークスペースルート解決 ---

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [[ -z "$ROOT" ]]; then
    # scripts/ → lean-build/ → skills/ → .github/ → workspace-root
    ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
fi

S2IL_DIR="${ROOT}/S2IL"
OUT_FILE="${ROOT}/S2IL/_agent/symbol-map.jsonl"

if [[ ! -d "$S2IL_DIR" ]]; then
    echo "[update-symbol-map] S2IL directory not found: $S2IL_DIR" >&2
    exit 1
fi

# 出力先ディレクトリ確保
OUT_DIR="$(dirname "$OUT_FILE")"
mkdir -p "$OUT_DIR"

# --- Lean ファイルを走査してシンボルを抽出 ---

# 宣言キーワードパターン:
#   先頭の空白、修飾子 (private|protected|noncomputable|unsafe|partial)、属性 (@[...])
#   に続く宣言キーワードと名前を抽出する
DECL_RE='^\s*(private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*(@\[.*\]\s+)*(def|theorem|lemma|instance|abbrev|structure|inductive|class|axiom|opaque)\s+([^[:space:]:{\[(]+)'

ENTRY_COUNT=0
TMP_OUT=$(mktemp)

# bash 4.3+ の nameref で namespace スタックを管理するため、
# python3 がある場合は処理全体をそちらに委譲する（確実な実装のため）

if command -v python3 &>/dev/null; then

python3 - "$S2IL_DIR" "$ROOT" "$TMP_OUT" <<'PYEOF'
import sys, os, re, json

s2il_dir = sys.argv[1]
root      = sys.argv[2]
out_path  = sys.argv[3]

decl_re = re.compile(
    r'^\s*(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)'
    r'(?:@\[.*?\]\s+)?'
    r'(?P<kind>def|theorem|lemma|instance|abbrev|structure|inductive|class|axiom|opaque)\s+'
    r'(?P<name>\S+)'
)

entries = []

for dirpath, _, filenames in os.walk(s2il_dir):
    for fname in filenames:
        if not fname.endswith('.lean'):
            continue
        fpath = os.path.join(dirpath, fname)
        rel_path = os.path.relpath(fpath, root).replace(os.sep, '/')

        with open(fpath, encoding='utf-8', errors='replace') as f:
            lines = f.read().splitlines()

        ns_stack = []
        line_no = 0

        for line in lines:
            line_no += 1
            # コメント行はスキップ
            if re.match(r'^\s*--', line):
                continue

            # namespace 追跡
            m = re.match(r'^\s*namespace\s+(\S+)', line)
            if m:
                ns_stack.append(m.group(1))
                continue

            m = re.match(r'^\s*end\s+(\S+)', line)
            if m:
                if ns_stack:
                    ns_stack.pop()
                continue

            m = re.match(r'^\s*end\s*$', line)
            if m:
                if ns_stack:
                    ns_stack.pop()
                continue

            # 宣言抽出
            m = decl_re.match(line)
            if not m:
                continue

            kind      = m.group('kind')
            raw_name  = m.group('name')
            mods      = m.group('mods') or ''
            is_private = bool(re.search(r'\bprivate\b', mods))

            # 末尾の記号を除去
            raw_name = re.split(r'[:\s\{\(\[]', raw_name)[0]
            if not raw_name:
                continue

            # namespace による修飾
            if ns_stack and '.' not in raw_name:
                symbol = '.'.join(ns_stack) + '.' + raw_name
            else:
                symbol = raw_name

            # シグネチャプレビュー (`:=` または `where` までを 1 行化、200 字上限)
            sig_parts = []
            end_idx = min(line_no - 1 + 20, len(lines) - 1)
            for j in range(line_no - 1, end_idx + 1):
                l = lines[j]
                ci = l.find('--')
                if ci >= 0:
                    l = l[:ci]
                sig_parts.append(l)
                if re.search(r':=|\bwhere\b', l):
                    break
            joined = ' '.join(sig_parts)
            cut_idx = joined.find(':=')
            if cut_idx >= 0:
                joined = joined[:cut_idx]
            joined = re.sub(r'\s+', ' ', joined).strip()
            if len(joined) > 200:
                joined = joined[:197] + '...'

            obj = {"file": rel_path, "line": line_no, "kind": kind, "symbol": symbol}
            if is_private:
                obj["scope"] = "private"
            obj["sig"] = joined
            entries.append(json.dumps(obj, ensure_ascii=False))

with open(out_path, 'w', encoding='utf-8') as f:
    f.write('\n'.join(entries))
    if entries:
        f.write('\n')
PYEOF

ENTRY_COUNT=$(wc -l < "$TMP_OUT" | tr -d ' ')
mv "$TMP_OUT" "$OUT_FILE"

else
    # python3 なし: bash + grep/sed によるフォールバック実装（namespace 追跡なし）
    warn() { echo "[update-symbol-map] WARN: $*" >&2 ;}
    warn "python3 が見つかりません。フォールバック実装を使用します（namespace 追跡なし）"

    while IFS= read -r -d '' fpath; do
        REL_PATH="${fpath#"$ROOT/"}"
        REL_PATH="${REL_PATH//\\//}"  # バックスラッシュ→スラッシュ（念のため）

        while IFS= read -r line; do
            # コメント行スキップ
            echo "$line" | grep -qE '^\s*--' && continue

            if [[ "$line" =~ $DECL_RE ]]; then
                KIND="${BASH_REMATCH[3]}"
                RAW_NAME="${BASH_REMATCH[4]}"
                # 末尾の記号除去
                RAW_NAME="${RAW_NAME%%[:\ \{\(\[]*}"
                [[ -z "$RAW_NAME" ]] && continue

                # JSON エスケープ（最小限）
                ESC_SYMBOL="${RAW_NAME//\\/\\\\}"
                ESC_SYMBOL="${ESC_SYMBOL//\"/\\\"}"
                ESC_FILE="${REL_PATH//\\/\\\\}"
                ESC_FILE="${ESC_FILE//\"/\\\"}"
                ESC_KIND="${KIND//\\/\\\\}"
                ESC_KIND="${ESC_KIND//\"/\\\"}"

                printf '{"file":"%s","kind":"%s","symbol":"%s"}\n' \
                    "$ESC_FILE" "$ESC_KIND" "$ESC_SYMBOL" >> "$TMP_OUT"
            fi
        done < "$fpath"
    done < <(find "$S2IL_DIR" -name '*.lean' -print0)

    ENTRY_COUNT=$(wc -l < "$TMP_OUT" | tr -d ' ')
    mv "$TMP_OUT" "$OUT_FILE"
fi

echo "[update-symbol-map] $ENTRY_COUNT symbols -> $OUT_FILE"
