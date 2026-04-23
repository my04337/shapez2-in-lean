#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 my04337
# SPDX-License-Identifier: MIT
#
# transplant-proof.sh — REPL で完成した証明を .lean ファイルの sorry 行に移植する
#
# 使い方:
#   # --proof-file で証明テキストをファイルから渡す（推奨：エスケープ問題を回避）
#   .github/skills/lean-repl/scripts/transplant-proof.sh --file S2IL/Foo.lean --line 42 --proof-file Scratch/proof.lean
#
#   # --proof で証明テキストを直接渡す（1行の場合）
#   .github/skills/lean-repl/scripts/transplant-proof.sh --file S2IL/Foo.lean --line 42 --proof "by omega"
#
#   # --simp-stabilize で移植後に bare simp → simp only を一括変換
#   .github/skills/lean-repl/scripts/transplant-proof.sh --file S2IL/Foo.lean --line 42 --proof-file Scratch/proof.lean --simp-stabilize
#
#   # --dry-run でファイルを変更せず、置換結果をプレビュー
#   .github/skills/lean-repl/scripts/transplant-proof.sh --file S2IL/Foo.lean --line 42 --proof-file Scratch/proof.lean --dry-run
#
# 処理フロー:
#   1. 対象ファイルの指定行から sorry を検出
#   2. sorry 行のインデント深さを自動検出
#   3. 証明テキストの各行にインデントを適用
#   4. sorry を証明テキストで置換
#   5. UTF-8 で書き込み
#   6. --simp-stabilize 指定時: simp-stabilize.ps1 / .sh を chain 実行

set -euo pipefail

# --- ヘルパー関数 ---

info()  { printf '\033[36m[INFO] %s\033[0m\n' "$*" ;}
warn()  { printf '\033[33m[WARN] %s\033[0m\n' "$*" ;}
ok()    { printf '\033[32m[ OK ] %s\033[0m\n' "$*" ;}
err()   { printf '\033[31m[ERR ] %s\033[0m\n' "$*" ;}

# --- 引数パース ---

FILE=""
LINE=""
PROOF=""
PROOF_FILE=""
SIMP_STABILIZE=0
DRY_RUN=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --file)         FILE="$2"; shift 2 ;;
        --line)         LINE="$2"; shift 2 ;;
        --proof)        PROOF="$2"; shift 2 ;;
        --proof-file)   PROOF_FILE="$2"; shift 2 ;;
        --simp-stabilize) SIMP_STABILIZE=1; shift ;;
        --dry-run)      DRY_RUN=1; shift ;;
        *) err "不明なオプション: $1"; exit 1 ;;
    esac
done

# --- バリデーション ---

if [[ -z "$FILE" || -z "$LINE" ]]; then
    err "--file と --line は必須です"
    exit 1
fi

if [[ -z "$PROOF" && -z "$PROOF_FILE" ]]; then
    err "--proof または --proof-file のいずれかを指定してください"
    exit 1
fi

if [[ -n "$PROOF" && -n "$PROOF_FILE" ]]; then
    warn "--proof と --proof-file の両方が指定されました。--proof-file を優先します"
fi

if [[ ! -f "$FILE" ]]; then
    err "ファイルが見つかりません: $FILE"
    exit 1
fi

# --- 証明テキストの取得 ---

if [[ -n "$PROOF_FILE" ]]; then
    if [[ ! -f "$PROOF_FILE" ]]; then
        err "証明ファイルが見つかりません: $PROOF_FILE"
        exit 1
    fi
    PROOF_TEXT=$(cat "$PROOF_FILE" | sed 's/[[:space:]]*$//')  # trailing whitespace 除去
else
    PROOF_TEXT="$PROOF"
fi

if [[ -z "$(echo "$PROOF_TEXT" | tr -d '[:space:]')" ]]; then
    err "証明テキストが空です"
    exit 1
fi

PROOF_LINE_COUNT=$(echo "$PROOF_TEXT" | wc -l | tr -d ' ')
info "証明テキスト: $PROOF_LINE_COUNT 行"

# --- ファイル読み込み ---

# ファイルを配列に読み込む（0-based）
mapfile -t FILE_LINES < "$FILE"

LINE_IDX=$(( LINE - 1 ))
TOTAL_LINES=${#FILE_LINES[@]}

if (( LINE_IDX < 0 || LINE_IDX >= TOTAL_LINES )); then
    err "行番号 $LINE はファイルの範囲外です (1-$TOTAL_LINES)"
    exit 1
fi

TARGET_LINE="${FILE_LINES[$LINE_IDX]}"

# --- sorry 検出 ---

if ! echo "$TARGET_LINE" | grep -qP '\bsorry\b' 2>/dev/null && \
   ! echo "$TARGET_LINE" | grep -q '\bsorry\b'; then
    err "行 $LINE に sorry が見つかりません: '$(echo "$TARGET_LINE" | sed 's/^[[:space:]]*//')'"
    exit 1
fi

info "対象行 L${LINE}: ${TARGET_LINE}"

# --- インデント検出 ---

# sorry が行の主要コンテンツ（行頭の空白 + sorry のみ）かどうか判定
TRIMMED="${TARGET_LINE#"${TARGET_LINE%%[! ]*}"}"  # leading whitespace 除去
TRIMMED="${TRIMMED%"${TRIMMED##*[! ]}"}"           # trailing whitespace 除去
IS_SORRY_ONLY=0
if [[ "$TRIMMED" == "sorry" ]]; then
    IS_SORRY_ONLY=1
fi

# ベースインデント計算
BASE_INDENT=""
if (( IS_SORRY_ONLY )); then
    # sorry 単独行: 行のインデントを取得
    BASE_INDENT="${TARGET_LINE%%[! ]*}"  # 先頭の空白のみ抽出
    # タブをスペース2つに変換
    BASE_INDENT="${BASE_INDENT//$'\t'/  }"
    SORRY_COL=${#BASE_INDENT}
else
    # インライン sorry: sorry の列位置を計算
    BEFORE_SORRY="${TARGET_LINE%%sorry*}"
    SORRY_COL=${#BEFORE_SORRY}
    BASE_INDENT=$(printf '%*s' "$SORRY_COL" '')
fi

info "ベースインデント: ${#BASE_INDENT} 文字 (sorry-only: $IS_SORRY_ONLY)"

# --- 証明テキストの最小インデント検出 ---

MIN_INDENT=99999
while IFS= read -r pl; do
    trimmed_pl="${pl#"${pl%%[! ]*}"}"
    if [[ -n "$trimmed_pl" ]]; then
        # 行頭スペース数を計算（タブは2スペース換算）
        leading=0
        for (( ci=0; ci<${#pl}; ci++ )); do
            ch="${pl:$ci:1}"
            if [[ "$ch" == " " ]]; then
                (( leading++ ))
            elif [[ "$ch" == $'\t' ]]; then
                (( leading += 2 ))
            else
                break
            fi
        done
        if (( leading < MIN_INDENT )); then
            MIN_INDENT=$leading
        fi
    fi
done <<< "$PROOF_TEXT"

if (( MIN_INDENT == 99999 )); then MIN_INDENT=0; fi

# --- 証明テキストにインデントを適用 ---

INDENTED_PROOF_LINES=()
line_i=0
while IFS= read -r pl; do
    trimmed_pl="${pl#"${pl%%[! ]*}"}"
    if [[ -z "$trimmed_pl" ]]; then
        INDENTED_PROOF_LINES+=("")
        (( line_i++ ))
        continue
    fi

    # 元のインデントを除去（先頭 MIN_INDENT 文字分）
    stripped_len=${#pl}
    strip_len=$(( MIN_INDENT < stripped_len ? MIN_INDENT : stripped_len ))
    stripped="${pl:$strip_len}"
    # タブをスペースに変換
    stripped="${stripped//$'\t'/  }"

    if (( line_i == 0 && IS_SORRY_ONLY == 0 )); then
        # 最初の行 (インライン sorry): 追加インデントなし
        INDENTED_PROOF_LINES+=("$stripped")
    else
        INDENTED_PROOF_LINES+=("${BASE_INDENT}${stripped}")
    fi
    (( line_i++ ))
done <<< "$PROOF_TEXT"

# --- sorry 置換 ---

RESULT_LINES=()

if (( IS_SORRY_ONLY )); then
    # sorry 単独行: 行全体を置換（1行または複数行）
    inserted=0
    for (( i=0; i<TOTAL_LINES; i++ )); do
        if (( i == LINE_IDX )); then
            for ipl in "${INDENTED_PROOF_LINES[@]}"; do
                RESULT_LINES+=("$ipl")
            done
            inserted=1
        else
            RESULT_LINES+=("${FILE_LINES[$i]}")
        fi
    done
else
    # インライン sorry: sorry 部分だけを置換
    BEFORE_SORRY="${TARGET_LINE:0:$SORRY_COL}"
    AFTER_SORRY="${TARGET_LINE:$(( SORRY_COL + 5 ))}"  # "sorry" は 5 文字

    PROOF_COUNT=${#INDENTED_PROOF_LINES[@]}

    for (( i=0; i<TOTAL_LINES; i++ )); do
        if (( i == LINE_IDX )); then
            if (( PROOF_COUNT == 1 )); then
                # 1 行証明: インラインで置換
                RESULT_LINES+=("${BEFORE_SORRY}${INDENTED_PROOF_LINES[0]}${AFTER_SORRY}")
            else
                # 複数行証明: 最初の行はインライン、残りを後続行として挿入
                RESULT_LINES+=("${BEFORE_SORRY}${INDENTED_PROOF_LINES[0]}")
                for (( pi=1; pi<PROOF_COUNT-1; pi++ )); do
                    RESULT_LINES+=("${INDENTED_PROOF_LINES[$pi]}")
                done
                # 最後の行に afterSorry を追加
                trimmed_after="${AFTER_SORRY%"${AFTER_SORRY##*[! ]}"}"
                if [[ -n "$trimmed_after" ]]; then
                    RESULT_LINES+=("${INDENTED_PROOF_LINES[$((PROOF_COUNT-1))]}${AFTER_SORRY}")
                else
                    RESULT_LINES+=("${INDENTED_PROOF_LINES[$((PROOF_COUNT-1))]}")
                fi
            fi
        else
            RESULT_LINES+=("${FILE_LINES[$i]}")
        fi
    done
fi

# --- プレビュー ---

RESULT_LINE_COUNT=${#RESULT_LINES[@]}
START_PREVIEW=$(( LINE_IDX - 2 < 0 ? 0 : LINE_IDX - 2 ))
END_PREVIEW=$(( LINE_IDX + PROOF_LINE_COUNT + 1 ))
if (( END_PREVIEW >= RESULT_LINE_COUNT )); then
    END_PREVIEW=$(( RESULT_LINE_COUNT - 1 ))
fi

info "--- 置換結果プレビュー (L$(( START_PREVIEW + 1 ))-L$(( END_PREVIEW + 1 ))) ---"
for (( i=START_PREVIEW; i<=END_PREVIEW; i++ )); do
    if (( i >= LINE_IDX && i < LINE_IDX + PROOF_LINE_COUNT )); then
        marker=">"
    else
        marker=" "
    fi
    printf "%s L%d: %s\n" "$marker" "$(( i + 1 ))" "${RESULT_LINES[$i]}"
done
info "--- プレビュー終了 ---"

# --- ファイル書き込み ---

if (( DRY_RUN )); then
    warn "DryRun: ファイルは変更しません"
else
    # printf で結合（配列を LF 区切りで書き出し）
    {
        for (( i=0; i<${#RESULT_LINES[@]}; i++ )); do
            if (( i > 0 )); then printf '\n'; fi
            printf '%s' "${RESULT_LINES[$i]}"
        done
    } > "$FILE"
    ok "移植完了: $FILE L$LINE の sorry を置換しました ($PROOF_LINE_COUNT 行)"
fi

# --- simp 安定化 ---

if (( SIMP_STABILIZE && !DRY_RUN )); then
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    SIMP_SCRIPT="$SCRIPT_DIR/../../lean-simp-guide/scripts/simp-stabilize.ps1"
    SIMP_SCRIPT_SH="$SCRIPT_DIR/../../lean-simp-guide/scripts/simp-stabilize.sh"

    if [[ -f "$SIMP_SCRIPT_SH" ]]; then
        info "simp-stabilize.sh を chain 実行します..."
        bash "$SIMP_SCRIPT_SH" --file "$FILE"
    elif command -v pwsh &>/dev/null && [[ -f "$SIMP_SCRIPT" ]]; then
        info "simp-stabilize.ps1 を chain 実行します..."
        pwsh -ExecutionPolicy Bypass -NoProfile -File "$SIMP_SCRIPT" -File "$FILE"
    else
        warn "simp-stabilize スクリプトが見つかりません"
        warn "手動で bare simp → simp only を実行してください"
    fi
elif (( SIMP_STABILIZE && DRY_RUN )); then
    warn "DryRun: simp-stabilize はスキップします"
fi
