# 計画・マイルストーン

Shapez2 in Lean (S2IL) プロジェクトの最終目標・大きな方針・層別の実行計画をまとめた入口ページ。

新しい証明に着手する前や、既存計画を見直すときにまずここを参照する。

---

## ファイル一覧

### プロジェクト全体の目標

| ファイル | 概要 |
|---|---|
| [MILESTONES.md](MILESTONES.md) | MAM 完全性に至る最終目標と、Data / Behavior / Flow / MAM の層構造 |

### Layer C 設計 / 実装計画

| ファイル | 概要 |
|---|---|
| [layer-c-flow-design-implementation-plan.md](layer-c-flow-design-implementation-plan.md) | Layer C Flow のスコープ、型付き Flow DSL 方針、C-1/C-2 実装ロードマップ |

### 確立済みアーキテクチャ資料

| ファイル | 概要 |
|---|---|
| [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) | Layer A/B のディレクトリ構造・設計原則・主要 theorem チェーンの正本 |

---

## いつ参照するか

| 作業 | 参照先 |
|---|---|
| プロジェクト全体の位置付けを確認 | `MILESTONES.md` |
| Layer C Flow の設計・実装に着手 | `layer-c-flow-design-implementation-plan.md` |
| Layer A/B の構造原則を確認 | `../s2il/architecture-layer-ab.md` |
| 個別 sorry の現状を確認 | `../../S2IL/_agent/sorry-plan.json` / `../../S2IL/_agent/sorry-goals.md` |
| 新しい証明計画を策定する | `../agent/proof-plan-current-focus-guide.md` |

## 新規ファイルの追加基準

- **追加する**: 新たな層の再構築計画や、大規模な証明調査が必要な場合
- **追加しない**: 小規模な証明（1〜2 sorry 程度）は `docs/s2il/` に知見として記録する
- **ファイル名**: 対象をケバブケースで（例: `stacker-equivariance-proof-plan.md`）
- 新規ファイルを追加したらこの README の一覧にも追記する
