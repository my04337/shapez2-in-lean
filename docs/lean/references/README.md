# 外部公式資料 — エージェント向け要約

このディレクトリには、Lean 4 の公式ページで紹介されている主要ドキュメントをクロールして要約したページが格納されています。

> ⚠️ **ライセンス注意**: このディレクトリ内のファイルは [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0) に基づく成果物を含みます。  
> 他のプロジェクト内ドキュメント（`docs/knowledge/`・`docs/lean/` 直下等）とは**内容を混在させないでください**。

---

## ファイル一覧

| ファイル | 元資料 | 概要 |
|---|---|---|
| [fp-in-lean-guide.md](fp-in-lean-guide.md) | [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) | FP in Lean 書籍の主要概念をエージェント向けに要約 |
| [lean-reference-guide.md](lean-reference-guide.md) | [The Lean Language Reference](https://lean-lang.org/doc/reference/latest/) | リファレンスマニュアルの逆引き索引・機能別参照ガイド |
| [mathlib-reference-guide.md](mathlib-reference-guide.md) | [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/) | Mathlib の分野別機能索引・タクティク一覧・逆引きリファレンス |
| [theorem-proving-guide.md](theorem-proving-guide.md) | [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) | TPIL4 書籍の定理証明概念をエージェント向けに要約 |

---

## 利用上の注意

- これらのファイルの**内容は変更しない**こと。元資料の要約であり、プロジェクト固有のナレッジを追記する場所ではない
- Lean 4 の構文やタクティクについてプロジェクト固有のノウハウを記録する場合は [`docs/knowledge/`](../../knowledge/) を使用すること
- タクティクの詳細リファレンスは [`docs/lean/tactics/`](../tactics/) を参照
