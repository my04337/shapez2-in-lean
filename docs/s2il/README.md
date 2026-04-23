# S2IL プロジェクト固有ナレッジ

S2IL（Shapez2 in Lean）プロジェクトに固有の技術知識・分析資料・補題インデックスを集約するディレクトリです。

一般的な Lean 4 やゲームシステムの情報とは区別し、**このプロジェクトのコードベース・証明チェーンに直結する知見**をここに配置します。

---

## ファイル一覧

### コードベース索引

| ファイル | 概要 |
|---|---|
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
| [proof-workflow-playbook.md](proof-workflow-playbook.md) | S2IL/AGENTS.md から移設した証明運用の詳細ルール（Proof-First-Test・REPL 優先・探索閾値） |

### 変更記録

| ファイル | 概要 |
|---|---|
| [crystal-bond-color-fix.md](crystal-bond-color-fix.md) | CrystalBond 色チェック修正記録。ゲーム実機テスト・確定ルール・影響範囲 |

---

## アーキテクチャ決定記録

### S2IL ディレクトリ構成（案D: 二層ハイブリッド）

> 出典: codebase-restructure-plan.md（計画完了・2026-04-17 削除）

S2IL は「Kernel（Gravity 非依存の横断基盤）＋ Operations（加工操作別モジュール）」の二層ハイブリッドを採用。

```text
S2IL/
  Kernel/                          -- 共通理論（Gravity 非依存の横断基盤）
    BFS/GenericBfs.lean
    Bond/CrystalBond.lean
    Transform/Rotate.lean, Rotate180Lemmas.lean
  Operations/                      -- 加工操作別モジュール
    Gravity/                       -- 線形チェーン: Defs→Equivariance→CommExt→PermInvariance→FoldlBridge→Facade
    Settled/                       -- Gravity 依存（全ファイルが Gravity を直接 import）
    Shatter/, Painter/, CrystalGenerator/, Cutter/, Stacker/, PinPusher/, ColorMixer/
  Shape/                           -- シェイプ定義
  Machine/Machine.lean             -- 加工装置ラッパー
  SettledShape.lean                -- 統合型（Settled + 操作の糊）
```

依存フロー: `Shape 層 → Kernel 層 → Operations 層 → 統合層`（単方向、循環なし）

**設計根拠**:
1. **Kernel は Gravity 非依存に厳格限定**: BFS・Bond・Transform の 3 サブディレクトリのみ。上向き依存ゼロ
2. **Operations/Gravity/ は線形チェーン保持**: 6 段チェーンが閉じている
3. **Operations/Settled/ は Gravity 依存のため Operations 配置**: Kernel に置くと上向き依存が発生
4. **小規模操作も `Operations/X/` に統一**: 将来の等変性証明追加時にファイル追加が自然
5. **依存フローの単方向性**: `Kernel → Gravity → Settled → {Stacker, Cutter, PinPusher}`

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
| 新しい証明に着手する前 | `equivariance-proof-patterns.md` + `gravity-equivariance-analysis.md` で証明パターンを確認 |
| 等変性証明を書く | `equivariance-proof-patterns.md` で使えるパターンを確認 |
| Gravity 関連の作業 | `gravity-equivariance-analysis.md` |
| sorry の状態を確認 | `S2IL/_agent/sorry-plan.json` |
| CrystalBond の仕様変更を理解 | `crystal-bond-color-fix.md` |

### 新規ファイルの追加基準

- **追加する**: S2IL プロジェクトのコードベースに直結する技術知見・分析結果
- **追加しない**: 一般的な Lean 4 Tips → `docs/lean/`、ゲーム仕様 → `docs/shapez2/`、開発計画 → `docs/plans/`
- **ファイル名**: ケバブケースで内容を表す（例: `stacker-equivariance-analysis.md`）
- 新規ファイルを追加した際は、この README のファイル一覧にも追記すること
