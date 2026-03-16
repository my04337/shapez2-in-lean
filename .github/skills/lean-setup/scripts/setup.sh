#!/usr/bin/env bash
# lean-setup: elan ツールチェインの PATH 解決と動作確認 (bash/zsh)
set -euo pipefail

ELAN_BIN="$HOME/.elan/bin"

# 1. elan の存在確認
if [ ! -d "$ELAN_BIN" ]; then
    echo "ERROR: elan が見つかりません: $ELAN_BIN" >&2
    echo "インストール: https://github.com/leanprover/elan#installation" >&2
    exit 1
fi

# 2. PATH に追加
case ":$PATH:" in
    *":$ELAN_BIN:"*) echo "PATH 設定済み: $ELAN_BIN" ;;
    *)
        export PATH="$ELAN_BIN:$PATH"
        echo "PATH に追加: $ELAN_BIN"
        ;;
esac

# 3. 動作確認
echo "--- lake ---"
lake --version
echo "--- lean ---"
lean --version
