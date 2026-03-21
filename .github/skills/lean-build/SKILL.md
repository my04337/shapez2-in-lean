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

PATH 解決 → ビルドをまとめて行う。
シェル名を前置せず、スクリプトを直接実行すること。

- **Windows**: `.github/skills/lean-build/scripts/build.ps1`
- **macOS / Linux**: `.github/skills/lean-build/scripts/build.sh`

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

## 構造化出力

スクリプトはビルド結果を以下の形式で出力する:

- **マーカー区切りサマリー** (stdout): `=== BUILD DIAGNOSTICS ===` 〜 `=== END DIAGNOSTICS ===`
- **全ログ**: `.lake/build-log.txt`
- **診断 JSONL**: `.lake/build-diagnostics.jsonl`（1行1JSON）

サマリーにはエラー・sorry・警告の件数と、優先度順の診断メッセージ（最大20件）が含まれる。

診断の詳細な分析・トリアージは **lean-diagnostics** スキルを参照。

## トラブルシューティング

- `lake` が見つからない → **lean-setup** スキルを参照
- ビルドエラー → サマリーの `[error]` 行を確認、詳細は `.lake/build-log.txt` を参照
- sorry 検出 → サマリーの `[sorry]` 行で未証明箇所を特定
- 依存解決エラー → `--update` オプションで再ビルド
- toolchain バージョン不一致 → `lean-toolchain` の内容を確認
