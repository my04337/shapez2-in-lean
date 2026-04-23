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
| [Lean 4 命名規則リファレンス](naming-conventions.md) | Lean 4 / Mathlib の一般的な命名規則。S2IL 固有ルールは S2IL/AGENTS.md を参照 |
| [Lean 4 ツールチェインガイド](toolchain-guide.md) | elan・Lake・Lean 等のツールチェイン構成要素の名称と役割 |
| [タクティク索引](tactics/index.md) | Lean 4 / Mathlib タクティク全索引（300+ エントリ）・詳細ページ群 |
| [Aesop 活用ガイド](aesop-guide.md) | Aesop のルール設計基準・良い/悪い使い方・デバッグ方法 |
| [Duper 活用ガイド](duper-guide.md) | Duper (超位置推論 ATP) の良い/悪い使い方・S2IL での活用指針 |
| [Plausible 活用ガイド](plausible-guide.md) | Plausible のランダムテスト・良い/悪い使い方・S2IL 型対応表 |

### 証明ノウハウ

| ドキュメント | 概要 |
|---|---|
| [Lean 4 証明 Tips](lean-proof-tips.md) | String 型・simp only vs decide・帰納法・rcases 等の実践的 Tips |
| [Mathlib / Batteries Tips](mathlib-batteries-tips.md) | 依存関係・simp 最適化・List.Perm・decide/omega 等のノウハウ |
| [String ラウンドトリップ証明](string-roundtrip-proof.md) | String ラウンドトリップ証明パターン。失敗/成功アプローチ・実装詳細 |

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

### arXiv 論文リファレンス

Lean 4 / 定理証明に関連する学術論文の要約・分析。[`arxiv/`](arxiv/) に分離配置。各論文のライセンスは個別 README.md を参照。

| ドキュメント | 概要 |
|---|---|
| [Mechanic: Sorrifier-Driven Formal Decomposition](arxiv/2603.24465-mechanic-sorrifier/summary.md) | sorry 駆動の形式分解ワークフロー。S2IL の sorry 解消戦略への示唆を含む |
