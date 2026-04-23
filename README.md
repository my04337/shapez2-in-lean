# shapez2-in-lean

> **注意 / Note:** これは非公式の[Shapez2](https://shapez2.com/)用ツールです。Shapez2の開発元とは一切関係ありません。  
> This is an unofficial tool for [Shapez2](https://shapez2.com/). It is not affiliated with the developers of Shapez2 in any way.

## 概要 / Overview

[Lean言語](https://lean-lang.org/)を用いてShapez2のロジックを形式的に定義し、MAM (Make Anything Machine) の検証を行えるようにすることを目標としたプロジェクトです。  
This project aims to formally define Shapez2 logic using the [Lean language](https://lean-lang.org/) and enable verification of MAM (Make Anything Machine) configurations.

作者自身がLean言語に不慣れなため、学習を兼ねながら本プロジェクトを開発しています。  
The author is still learning Lean, so this project is being developed as a learning exercise as well.

なお、本プロジェクトの開発の一部には生成AI (GitHub Copilot) を利用しています。  
Note: Part of the development of this project uses generative AI (GitHub Copilot).

> **現状 / Status:** フェーズ 1（Shape/加工装置の形式的定義・証明）完了。Shape Code の型定義・シリアライズ、切断・回転・積層・着色・ピン押し・結晶化・重力処理・散砕 など全加工操作の実装と正当性証明（sorry 0 件）が完了しています。  
> **Status:** Phase 1 complete — All shape types, serialization, and shape-processing operations (cut, rotate, stack, paint, pin-push, crystallize, gravity, shatter) are formally defined and proved (0 sorries).

## 前提条件

- [VS Code](https://code.visualstudio.com/)
- [elan](https://github.com/leanprover/elan#installation) (Lean 4 バージョンマネージャー)
  - **Windows**: `winget install leanprover.elan` またはインストーラを[リリースページ](https://github.com/leanprover/elan/releases)から取得
  - **macOS / Linux**: `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`
  - インストール後、シェルを再起動して `elan` / `lake` コマンドを有効化してください
  - `lean-toolchain` に記載されたバージョンの Lean が elan によって自動でダウンロードされます

## 初回セットアップ（クリーンビルド）

リポジトリをクローン・チェックアウトした直後、または `.lake/` ディレクトリを削除した後は以下の手順でビルド環境を整えます。

```powershell
# 1. 依存パッケージ（Mathlib 等）をダウンロード
#    lean-toolchain に指定された Lean バージョンも elan が自動取得します
lake update

# 2. Mathlib の prebuilt olean キャッシュをダウンロード
#    この手順でキャッシュが ~/.cache/mathlib/ に保存され、ビルド時間を大幅に短縮できます
#    （Mathlib をソースからコンパイルすると 30〜60 分以上かかる部分が約 3 分になります）
lake exe cache get

# 3. プロジェクトをビルド
lake build
```

> **`lake update` でエラーになる場合**: `package not found on Reservoir` と表示される場合、
> `lakefile.toml` の `scope` 指定を `git` URL に変更してください。
>
> ```toml
> [[require]]
> name = "mathlib"
> git = "https://github.com/leanprover-community/mathlib4"
> ```
>
> 変更後、再度 `lake update` を実行してください。

> **Windows での注意**: 手順 2 は VS Code を閉じた状態で実行するのが確実です。
> VS Code の Lean 拡張がファイルをメモリマップで保持していると `os error 1224` でキャッシュの書き込みに失敗しますが、
> `~/.cache/mathlib/` に既存の `.ltar` ファイルがある場合はエラーが出ても手順 3 のビルドは問題なく動作します。

## ビルド・実行

VS Code でこのリポジトリを開き、**Ctrl+Shift+B** を押すとビルドが一括で行われます。

コマンドラインから実行する場合:

```powershell
# ビルド
lake build

# 開発ツール（S2IL 依存 — 依存グラフ・シンボルマップ・証明統計）
lake exe s2il-toolkit --help
lake exe s2il-toolkit depgraph --json --output .lake/depgraph.json
lake exe s2il-toolkit proof-stats

# 診断ツール（S2IL 非依存 — S2IL ビルドエラー時も動作）
lake exe s2il-diag sorry-list
```

## バージョンアップとビルド高速化

### バージョン管理の方針

このプロジェクトは `lakefile.toml` の `rev` で Mathlib のバージョンを**タグで明示的に固定**しています。

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.29.0"   ← Mathlib のリリースタグ
```

また `lean-toolchain` は Mathlib が要求する Lean バージョンと**常に一致させる**必要があります。

```
leanprover/lean4:v4.29.0   ← lean-toolchain の内容
```

> **注意**: Lean の最新安定版（例: `v4.29.0`）が存在していても、Mathlib 側のタグがその版に対応するまでは
> Lean のバージョンを先行して上げることはできません。必ず Mathlib のリリースタグを確認してから更新してください。

### Lean / Mathlib のバージョンアップ手順

新しい Mathlib リリースタグ（例: `v4.30.0`）が出たときの更新手順です。

**1. `lakefile.toml` の `rev` を新しいタグに変更する**

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.30.0"   ← 新しいタグに書き換え
```

**2. `lake update` を実行して `lake-manifest.json` を更新する**

```powershell
lake update
```

**3. Mathlib が要求する Lean バージョンを確認して `lean-toolchain` を更新する**

```powershell
Get-Content .lake/packages/mathlib/lean-toolchain   # Windows
cat .lake/packages/mathlib/lean-toolchain           # macOS / Linux
```

表示されたバージョン（例: `leanprover/lean4:v4.30.0`）を `lean-toolchain` に書き込みます。
elan が自動的に新しい Lean バージョンをダウンロードします。

**4. prebuilt olean キャッシュを取得して再ビルドする**（後述）

### Mathlib prebuilt olean キャッシュの取得

`lean-toolchain` と Mathlib の要求バージョンが一致している場合、prebuilt olean キャッシュを利用して
Mathlib のローカルコンパイルを回避できます（数十分 → 約3分）。

```powershell
# Windows (PowerShell)
lake exe cache get
```

```bash
# macOS / Linux
lake exe cache get
```

> **Windows 注意**: VS Code の Lean 拡張が起動中だと `os error 1224` でキャッシュ書き込みに失敗することがあります。
> 既存の `.ltar` ファイルが正しいバージョンであれば、エラーが出ても `lake build` は問題なく動作します。
> 初回インストール直後など `~/.cache/mathlib/` が空の場合は、VS Code を閉じてから実行してください。

### ビルド時間の目安 (16 コアマシン)

| 状況 | ビルド時間 |
|---|---|
| キャッシュなし（Mathlib をソースからコンパイル） | 30〜60 分以上 |
| キャッシュ有り・初回（prebuilt olean を展開） | 約 3 分 |
| キャッシュ有り・増分（変更なし） | 約 1〜2 秒 |

## 免責事項

本ツールの出力結果が正しいことは保証しません。検証結果はあくまで参考情報としてご利用ください。

## ライセンス

[MIT License](LICENSE)

---

Copyright (c) 2026 my04337
