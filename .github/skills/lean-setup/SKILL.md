---
name: lean-setup
description: 'Lean 4 ツールチェイン (elan/lake/lean) のパスを解決し、ターミナルやタスクから利用可能にする。Use when: lean or lake command is not found, PATH setup, elan toolchain resolution, environment configuration.'
argument-hint: 'ツールチェインのセットアップや PATH 問題のトラブルシュートを行います'
---

# Lean ツールチェインセットアップ

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

elan の存在確認、PATH 追加、動作確認をまとめて行う:

- **Windows (PowerShell 7)**: [setup.ps1](./scripts/setup.ps1)
- **macOS / Linux (bash/zsh)**: [setup.sh](./scripts/setup.sh)

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
