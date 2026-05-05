# Lean ツールチェインセットアップ

> 詳細参照: 通常は [`lean-tooling`](../SKILL.md) を入口にし、詳しい手順が必要なときだけ本ファイルを読む。

elan でインストールされた Lean 4 ツールチェイン (lean, lake 等) の PATH を解決し利用可能にする。

## 前提条件

- [elan](https://github.com/leanprover/elan) がインストール済みであること

## ツールチェインの場所

| OS | デフォルトパス |
|---|---|
| Windows | `%USERPROFILE%\.elan\bin` |
| macOS / Linux | `~/.elan/bin` |

## 手順

### 1. セットアップスクリプトの実行

elan の存在確認、PATH 追加、動作確認をまとめて行う。
シェル名を前置せず、スクリプトを直接実行すること。

- **Windows**: `.github/skills/lean-tooling/scripts/setup.ps1`
- **macOS / Linux**: `.github/skills/lean-tooling/scripts/setup.sh`

### 2. VS Code タスクでの PATH 解決

`.vscode/tasks.json` の `options.env` で PATH を補う:

```json
"options": {
    "env": {
        "PATH": "${env:USERPROFILE}\\.elan\\bin;${env:PATH}"
    }
}
```

## トラブルシューティング

- `lake` / `lean` が見つからない → PATH に elan の bin ディレクトリが含まれているか確認
- バージョン不一致 → `lean-toolchain` の内容と `elan show` の出力を比較
- elan 未インストール → https://github.com/leanprover/elan#installation
