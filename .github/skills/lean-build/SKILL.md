---
name: lean-build
description: 'Lean 4 プロジェクトを lake build でビルドする。Use when: build lean project, compile lean code, lake build, check compilation errors, resolve build failures.'
argument-hint: 'Lean プロジェクトのビルドを実行します'
---

# Lean プロジェクトのビルド

Lake を使用して Lean 4 プロジェクトをビルドする。

## 前提条件

- **lean-setup** スキルでツールチェインが利用可能であること
- プロジェクトルートに `lakefile.toml` (または `lakefile.lean`) が存在すること

## 手順

### 1. ビルドスクリプトの実行

PATH 解決 → ビルドをまとめて行う:

- **Windows (PowerShell 7)**: [build.ps1](./scripts/build.ps1)
- **macOS / Linux (bash/zsh)**: [build.sh](./scripts/build.sh)

オプション:

| オプション | 説明 |
|---|---|
| `-Clean` / `--clean` | `lake clean` 後にビルド |
| `-Update` / `--update` | `lake update` 後にビルド |
| `-Target <name>` / `--target <name>` | 特定ターゲットのみビルド |

### 2. ビルドターゲットの確認

`lakefile.toml` の `defaultTargets` でデフォルト対象が定義されている:

```toml
defaultTargets = ["s2il"]

[[lean_lib]]
name = "S2IL"

[[lean_exe]]
name = "s2il"
root = "Main"
```

### 3. VS Code からのビルド

Ctrl+Shift+B で `lake build` タスクが実行される (`.vscode/tasks.json` で設定済み)。

## トラブルシューティング

- `lake` が見つからない → **lean-setup** スキルを参照
- ビルドエラー → エラーメッセージの行番号・ファイルを確認し修正
- 依存解決エラー → `--update` オプションで再ビルド
- toolchain バージョン不一致 → `lean-toolchain` の内容を確認
