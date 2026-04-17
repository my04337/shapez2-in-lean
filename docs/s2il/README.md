# S2IL プロジェクト固有ナレッジ

S2IL（Shapez2 in Lean）プロジェクトに固有の技術知識・分析資料・補題インデックスを集約するディレクトリです。

一般的な Lean 4 やゲームシステムの情報とは区別し、**このプロジェクトのコードベース・証明チェーンに直結する知見**をここに配置します。

---

## ファイル一覧

### コードベース索引

| ファイル | 概要 |
|---|---|
| [s2il-lemma-index.md](s2il-lemma-index.md) | **必読**: Gravity 4 ファイル構造・主要補題一覧・sorry 状態・依存関係マップ |
| [game-config.md](game-config.md) | GameConfig（ゲーム設定）の設計方針・プリセット一覧 |
| [library-reference.md](library-reference.md) | 導入済みライブラリ・ツール一覧。利用状態・スキル整備・バージョン追従状況 |

### 証明パターン・分析

| ファイル | 概要 |
|---|---|
| [equivariance-proof-patterns.md](equivariance-proof-patterns.md) | 5 つの等変性証明パターン。pointwise-any→foldl・BFS 列挙・方角素・演算∘回転 |
| [bfs-equivariance-proof.md](bfs-equivariance-proof.md) | CrystalBond BFS の 180° 等変性証明。失敗/成功戦略・補助補題 |
| [false-theorem-catalog.md](false-theorem-catalog.md) | 偽定理カタログ。Gravity 証明チェーンで発見された偽定理・棄却済みアプローチ一覧 |
| [gravity-equivariance-analysis.md](gravity-equivariance-analysis.md) | Gravity `process_rotate180` 証明知識。`any_pred_ext` パターン・`placeFallingUnit` 非可換性・`spb_no_mutual` 証明戦略 |
| [gravity-issettled-matrix.md](gravity-issettled-matrix.md) | 全加工装置の gravity 利用・IsSettled 必要性マトリクス |

### 変更記録

| ファイル | 概要 |
|---|---|
| [crystal-bond-color-fix.md](crystal-bond-color-fix.md) | CrystalBond 色チェック修正記録。ゲーム実機テスト・確定ルール・影響範囲 |

---

## アーキテクチャ決定記録

### `FallingUnit.cluster` への接続性証明の型埋め込み却下

> 出典: pin-fallingunit-design-review.md §3.2（レビュー完了・削除済み）

`FallingUnit.cluster` に `h_connected : ∀ q1 q2, GenericReachable ...` を持たせる代替設計を検討し、**却下** した。

| 観点 | 現実装（仮説で対応） | 型安全版（埋め込み） |
|---|---|---|
| 偽定理防止 | 仮説で事後対応 | 型レベルで事前排除 |
| 定義の単純さ | ✅ 簡潔 | 複雑化（Shape 依存が発生） |
| 既存証明への影響 | なし | 大規模破壊（~1,000行以上） |

**判断理由**: `allStructuralClustersList` が BFS で生成する以上、接続性は構成的に保証されている。`h_connected` 仮説による事後保証は実用的に十分であり、既存証明チェーンの大規模破壊は正当化されない。

---

## エージェント向け参照ガイダンス

### いつ参照するか

| 作業 | 参照先 |
|---|---|
| 新しい証明に着手する前 | `s2il-lemma-index.md` で対象ファイルの構造を把握 |
| 等変性証明を書く | `equivariance-proof-patterns.md` で使えるパターンを確認 |
| Gravity 関連の作業 | `gravity-equivariance-analysis.md` |
| sorry の状態を確認 | `s2il-lemma-index.md` の sorry 追跡セクション |
| CrystalBond の仕様変更を理解 | `crystal-bond-color-fix.md` |

### 新規ファイルの追加基準

- **追加する**: S2IL プロジェクトのコードベースに直結する技術知見・分析結果
- **追加しない**: 一般的な Lean 4 Tips → `docs/lean/`、ゲーム仕様 → `docs/shapez2/`、開発計画 → `docs/plans/`
- **ファイル名**: ケバブケースで内容を表す（例: `stacker-equivariance-analysis.md`）
- 新規ファイルを追加した際は、この README のファイル一覧にも追記すること
