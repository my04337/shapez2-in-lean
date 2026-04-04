# Lean 4 学習リソース

Lean 4 の理解を深めるための情報起点ページです。

## 公式情報

| リソース | URL | 概要 |
|---|---|---|
| 公式ページ | https://lean-lang.org | Lean 言語の公式サイト |
| Functional Programming in Lean | https://lean-lang.org/functional_programming_in_lean/ | Lean 言語の基礎について触れられています |
| Theorem Proving in Lean 4 | https://lean-lang.org/theorem_proving_in_lean4/ | Lean 4 を用いた定理証明について触れられています |
| The Lean Language Reference | https://lean-lang.org/doc/reference/latest/ | Lean 4 のリファレンスマニュアルです |

## プロジェクト内ガイド

### 実践ガイド

| ドキュメント | 概要 |
|---|---|
| [初学者のための数学用語簡易辞書](math-glossary.md) | ガイド中の高度な数学用語を初学者向けに簡潔に解説した辞書 |
| [Lean 4 ツールチェインガイド](toolchain-guide.md) | elan・Lake・Lean 等のツールチェイン構成要素の名称と役割 |
| [タクティク索引](tactics/index.md) | Lean 4 / Mathlib タクティク全索引（300+ エントリ）・詳細ページ群 |

### スキル固有の詳細リファレンス

対応するスキルディレクトリ配下の `references/` に配置されている。

| ドキュメント | 対応スキル | 概要 |
|---|---|---|
| [Lean REPL 詳細ガイド](../../.github/skills/lean-repl/references/repl-guide.md) | `lean-repl` | 3 モード・pickle 戦略・ユースケース集 |
| [Mathlib / Batteries 補題検索ガイド](../../.github/skills/lean-mathlib-search/references/mathlib-search-guide.md) | `lean-mathlib-search` | `exact?` / `apply?` / `#leansearch` / `#loogle` の使い分けと検索戦略マップ |

### 外部公式資料（Apache 2.0）

公式ドキュメントのエージェント向け要約。[`references/`](references/) に分離配置。内容変更不可。

| ドキュメント | 概要 |
|---|---|
| [Functional Programming in Lean — エージェント向け包括ガイド](references/fp-in-lean-guide.md) | FP in Lean 書籍の主要概念をエージェント向けに要約したガイド |
| [Theorem Proving in Lean 4 — エージェント向け定理証明ガイド](references/theorem-proving-guide.md) | TPIL4 書籍の定理証明概念をエージェント向けに要約したガイド |
| [The Lean Language Reference — エージェント向けリファレンス索引](references/lean-reference-guide.md) | リファレンスマニュアルの逆引き索引・機能別参照ガイド |
| [Mathlib — エージェント向けリファレンス索引](references/mathlib-reference-guide.md) | Mathlib の分野別機能索引・タクティク一覧・逆引きリファレンス |
