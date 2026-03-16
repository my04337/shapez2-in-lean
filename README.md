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

> **現状 / Status:** 開発初期段階のプレースホルダーです。Shapez2のロジック実装はこれからです。  
> This is an early-stage placeholder. Implementation of Shapez2 logic is yet to come.

## 前提条件

- [VS Code](https://code.visualstudio.com/)
- [elan](https://github.com/leanprover/elan#installation) (Lean 4 バージョンマネージャー)
  - インストール後、`lean-toolchain` の指定バージョンが自動で取得されます

## ビルド・実行

VS Code でこのリポジトリを開き、**Ctrl+Shift+B** を押すとビルド〜実行まで一括で行われます。

コマンドラインから実行する場合:

```powershell
# Windows (PowerShell 7)
pwsh.exe -File .github/skills/lean-run/scripts/run.ps1
```

```bash
# macOS / Linux
bash .github/skills/lean-run/scripts/setup.sh
```

## 免責事項

本ツールの出力結果が正しいことは保証しません。検証結果はあくまで参考情報としてご利用ください。

## ライセンス

[MIT License](LICENSE)

---

Copyright (c) 2026 my04337
