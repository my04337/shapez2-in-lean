#!/usr/bin/env bash
# Lean REPL デーモンプロセス (macOS / Linux)
#
# repl.sh --start から背景プロセスとして起動される。
# lake exe repl を管理し、ファイルベース IPC でコマンドを受け付ける。
#
# IPC プロトコル:
#   request.json  ← クライアントが書き込み → デーモンが読み取り・削除
#   response.json ← デーモンが書き込み
#   response.ready ← デーモンがシグナル作成 → クライアントが検知・削除
#   shutdown      ← クライアントが作成 → デーモンが検知して終了

set -uo pipefail
# 注意: set -e は使わない。デーモンのメインループでエラーが起きても継続する必要がある

# --- 引数解析 ---
SESSION_ID=""
REPO_ROOT=""
while [[ $# -gt 0 ]]; do
    case "$1" in
        --session-id) SESSION_ID="$2"; shift 2 ;;
        --repo-root)  REPO_ROOT="$2"; shift 2 ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

if [[ -z "$SESSION_ID" || -z "$REPO_ROOT" ]]; then
    echo "Error: --session-id and --repo-root are required" >&2
    exit 1
fi

SESSION_DIR="$REPO_ROOT/.repl/$SESSION_ID"
LOG_IN="$SESSION_DIR/_session-in.jsonl"
LOG_OUT="$SESSION_DIR/_session-out.jsonl"

# --- パス設定 ---
if [[ -d "$HOME/.elan/bin" ]]; then
    export PATH="$HOME/.elan/bin:$PATH"
fi

LAKE_BIN="$(command -v lake 2>/dev/null || true)"
if [[ -z "$LAKE_BIN" ]]; then
    echo "lake not found in PATH" > "$SESSION_DIR/error"
    exit 1
fi

cd "$REPO_ROOT"

# --- REPL プロセス起動 ---
# コプロセスとして lake exe repl を起動し、stdin/stdout を制御する
# coproc は bash 4+ で利用可能（macOS は bash 3 がデフォルトだが、
# このスクリプトは #!/usr/bin/env bash なので Homebrew bash 等を想定）

# FIFO ベースの IPC で REPL と通信する（coproc より移植性が高い）
REPL_IN_FIFO="$SESSION_DIR/_repl_stdin"
REPL_OUT_FIFO="$SESSION_DIR/_repl_stdout"
mkfifo "$REPL_IN_FIFO"
mkfifo "$REPL_OUT_FIFO"

# stderr を排出用ファイルにリダイレクト（バッファ溢れ防止）
REPL_STDERR="$SESSION_DIR/_repl_stderr.log"

# REPL プロセスを起動
"$LAKE_BIN" exe repl < "$REPL_IN_FIFO" > "$REPL_OUT_FIFO" 2>"$REPL_STDERR" &
REPL_PID=$!

# stdin への書き込み用 fd を開く（REPL プロセスの stdin FIFO）
exec 3>"$REPL_IN_FIFO"

# stdout からの読み取り用 fd を開く（REPL プロセスの stdout FIFO）
exec 4<"$REPL_OUT_FIFO"

# PID 記録
echo "$$" > "$SESSION_DIR/daemon.pid"
echo "$REPL_PID" > "$SESSION_DIR/repl.pid"

# --- クリーンアップ ---
cleanup() {
    # REPL プロセス停止
    if kill -0 "$REPL_PID" 2>/dev/null; then
        kill "$REPL_PID" 2>/dev/null || true
        wait "$REPL_PID" 2>/dev/null || true
    fi
    # fd クローズ
    exec 3>&- 2>/dev/null || true
    exec 4<&- 2>/dev/null || true
    # FIFO 削除
    rm -f "$REPL_IN_FIFO" "$REPL_OUT_FIFO"
    # PID ファイル削除
    rm -f "$SESSION_DIR/daemon.pid" "$SESSION_DIR/repl.pid" "$SESSION_DIR/ready"
}
trap cleanup EXIT

# --- REPL 応答読み取り ---
# REPL は各応答を pretty-printed JSON で出力し、末尾に空行が付く。
# 空行検出をメイン判定とし、タイムアウトをフォールバックとする。
read_repl_response() {
    local timeout_sec="${1:-120}"
    local lines=""
    local has_content=0
    local deadline=$((SECONDS + timeout_sec))

    while [[ $SECONDS -lt $deadline ]]; do
        # REPL プロセスの生存確認
        if ! kill -0 "$REPL_PID" 2>/dev/null; then
            break
        fi

        # タイムアウト付き読み取り（read -t はタイムアウト秒数。0.5 は bash 4+ で対応）
        local line=""
        if read -r -t 0.5 line <&4 2>/dev/null; then
            if [[ -z "$line" && $has_content -eq 1 ]]; then
                # 空行検出 → 応答完了
                break
            fi
            if [[ -n "${line// /}" ]]; then
                if [[ -n "$lines" ]]; then
                    lines="$lines"$'\n'"$line"
                else
                    lines="$line"
                fi
                has_content=1
            fi
        else
            # タイムアウト：応答中のデータがあれば静寂期間として完了
            if [[ $has_content -eq 1 ]]; then
                break
            fi
        fi
    done

    if [[ -z "$lines" ]]; then
        echo ""
        return 1
    fi
    echo "$lines"
    return 0
}

# --- JSON 1 行圧縮 ---
# jq が利用可能なら圧縮、なければ改行除去で近似
compact_json() {
    local input="$1"
    if command -v jq &>/dev/null; then
        echo "$input" | jq -c '.' 2>/dev/null || echo "$input" | tr -d '\n'
    else
        echo "$input" | tr -d '\n'
    fi
}

# --- Import 実行 ---
IMPORT_CMD='{"cmd": "import S2IL\nimport Mathlib.Tactic\nimport Plausible\nimport Duper"}'
echo "$IMPORT_CMD" >&3
echo "" >&3

echo "$IMPORT_CMD" >> "$LOG_IN"

IMPORT_RESP=""
if IMPORT_RESP=$(read_repl_response 120); then
    if [[ -n "$IMPORT_RESP" ]]; then
        ONE_LINE=$(compact_json "$IMPORT_RESP")
        echo "$ONE_LINE" >> "$LOG_OUT"
    fi
fi

# --- env/proofState リベース ---
# Persistent モードでは env/proofState がセッション全体で単調増加する。
# 各 Send バッチ内で相対的な番号付けを可能にするため、
# バッチ開始時のオフセットを記録し、env (> 0) と proofState を自動リベースする。
# env 0 は常に import 環境を指す（リベース対象外）。
ENV_BASE=0
PS_BASE=0

# --- 応答から env/proofState ベースを更新 ---
update_bases_from_response() {
    local resp_json="$1"

    if command -v jq &>/dev/null; then
        # env の追跡
        local env_val
        env_val=$(echo "$resp_json" | jq -r '.env // empty' 2>/dev/null || true)
        if [[ -n "$env_val" && "$env_val" != "null" ]]; then
            if [[ "$env_val" -gt "$ENV_BASE" ]]; then
                ENV_BASE=$env_val
            fi
        fi

        # proofState の追跡（tactic mode 応答）
        local ps_val
        ps_val=$(echo "$resp_json" | jq -r '.proofState // empty' 2>/dev/null || true)
        if [[ -n "$ps_val" && "$ps_val" != "null" ]]; then
            if [[ "$ps_val" -ge "$PS_BASE" ]]; then
                PS_BASE=$((ps_val + 1))
            fi
        fi

        # sorries[].proofState の追跡（command mode 応答）
        local sorry_ps_vals
        sorry_ps_vals=$(echo "$resp_json" | jq -r '.sorries[]?.proofState // empty' 2>/dev/null || true)
        if [[ -n "$sorry_ps_vals" ]]; then
            while IFS= read -r sp_val; do
                if [[ -n "$sp_val" && "$sp_val" != "null" && "$sp_val" -ge "$PS_BASE" ]]; then
                    PS_BASE=$((sp_val + 1))
                fi
            done <<< "$sorry_ps_vals"
        fi
    else
        # jq なし: grep ベースの簡易追跡
        local env_val
        env_val=$(echo "$resp_json" | grep -o '"env"[[:space:]]*:[[:space:]]*[0-9]*' | head -1 | grep -o '[0-9]*$' || true)
        if [[ -n "$env_val" && "$env_val" -gt "$ENV_BASE" ]]; then
            ENV_BASE=$env_val
        fi

        local ps_val
        ps_val=$(echo "$resp_json" | grep -o '"proofState"[[:space:]]*:[[:space:]]*[0-9]*' | head -1 | grep -o '[0-9]*$' || true)
        if [[ -n "$ps_val" && "$ps_val" -ge "$PS_BASE" ]]; then
            PS_BASE=$((ps_val + 1))
        fi
    fi
}

# --- コマンドの env/proofState をリベース ---
rebase_command() {
    local cmd="$1"
    local batch_env_base="$2"
    local batch_ps_base="$3"

    if command -v jq &>/dev/null; then
        # jq で JSON を操作
        local env_val ps_val modified
        modified="$cmd"

        env_val=$(echo "$cmd" | jq -r '.env // empty' 2>/dev/null || true)
        if [[ -n "$env_val" && "$env_val" != "null" && "$env_val" -gt 0 ]]; then
            local new_env=$((env_val + batch_env_base))
            modified=$(echo "$modified" | jq -c ".env = $new_env" 2>/dev/null || echo "$modified")
        fi

        ps_val=$(echo "$cmd" | jq -r '.proofState // empty' 2>/dev/null || true)
        if [[ -n "$ps_val" && "$ps_val" != "null" ]]; then
            local new_ps=$((ps_val + batch_ps_base))
            modified=$(echo "$modified" | jq -c ".proofState = $new_ps" 2>/dev/null || echo "$modified")
        fi

        echo "$modified"
    else
        # jq なし: sed ベースのリベース（正確ではないが基本的なケースをカバー）
        local result="$cmd"

        # env > 0 のリベース
        local env_val
        env_val=$(echo "$cmd" | grep -o '"env"[[:space:]]*:[[:space:]]*[0-9]*' | head -1 | grep -o '[0-9]*$' || true)
        if [[ -n "$env_val" && "$env_val" -gt 0 ]]; then
            local new_env=$((env_val + batch_env_base))
            result=$(echo "$result" | sed "s/\"env\"[[:space:]]*:[[:space:]]*$env_val/\"env\":$new_env/")
        fi

        # proofState のリベース
        local ps_val
        ps_val=$(echo "$cmd" | grep -o '"proofState"[[:space:]]*:[[:space:]]*[0-9]*' | head -1 | grep -o '[0-9]*$' || true)
        if [[ -n "$ps_val" ]]; then
            local new_ps=$((ps_val + batch_ps_base))
            result=$(echo "$result" | sed "s/\"proofState\"[[:space:]]*:[[:space:]]*$ps_val/\"proofState\":$new_ps/")
        fi

        echo "$result"
    fi
}

# --- メインループ ---
REQUEST_FILE="$SESSION_DIR/request.json"
RESPONSE_FILE="$SESSION_DIR/response.json"
RESPONSE_DONE="$SESSION_DIR/response.ready"
SHUTDOWN_FILE="$SESSION_DIR/shutdown"

# Ready シグナル: メインループ開始後（コマンド受付確定状態）で発行し、競合タイミングを防ぐ
echo "ok" > "$SESSION_DIR/ready"

while kill -0 "$REPL_PID" 2>/dev/null; do
    # シャットダウン検知
    if [[ -f "$SHUTDOWN_FILE" ]]; then
        break
    fi

    # リクエスト検知
    if [[ -f "$REQUEST_FILE" ]]; then
        # リクエスト読み取り
        CONTENT=$(cat "$REQUEST_FILE")
        rm -f "$REQUEST_FILE"

        echo "$CONTENT" >> "$LOG_IN"

        # コマンド分割（JSONL: 各行が1つの JSON コマンド、空行はスキップ）
        RESPONSES=""
        BATCH_ENV_BASE=$ENV_BASE
        BATCH_PS_BASE=$PS_BASE

        while IFS= read -r cmd_line; do
            # 空行・空白行をスキップ
            trimmed=$(echo "$cmd_line" | tr -d '[:space:]')
            if [[ -z "$trimmed" ]]; then
                continue
            fi

            # env/proofState リベース
            CMD_TO_SEND=$(rebase_command "$cmd_line" "$BATCH_ENV_BASE" "$BATCH_PS_BASE")

            # REPL に送信
            echo "$CMD_TO_SEND" >&3
            echo "" >&3

            # 応答読み取り
            RESP=""
            if RESP=$(read_repl_response 120); then
                if [[ -n "$RESP" ]]; then
                    ONE_LINE=$(compact_json "$RESP")
                    update_bases_from_response "$ONE_LINE"
                    if [[ -n "$RESPONSES" ]]; then
                        RESPONSES="$RESPONSES"$'\n'"$ONE_LINE"
                    else
                        RESPONSES="$ONE_LINE"
                    fi
                else
                    ERR_JSON='{"error":"response_timeout","message":"No response from REPL within timeout"}'
                    if [[ -n "$RESPONSES" ]]; then
                        RESPONSES="$RESPONSES"$'\n'"$ERR_JSON"
                    else
                        RESPONSES="$ERR_JSON"
                    fi
                fi
            else
                ERR_JSON='{"error":"response_timeout","message":"No response from REPL within timeout"}'
                if [[ -n "$RESPONSES" ]]; then
                    RESPONSES="$RESPONSES"$'\n'"$ERR_JSON"
                else
                    RESPONSES="$ERR_JSON"
                fi
            fi
        done <<< "$CONTENT"

        # 応答書き込み
        echo "$RESPONSES" > "$RESPONSE_FILE"
        echo "$RESPONSES" >> "$LOG_OUT"
        echo "ok" > "$RESPONSE_DONE"
    fi

    # ポーリング間隔（CPU 負荷軽減）
    sleep 0.03
done
