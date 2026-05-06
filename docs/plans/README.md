# 計画・マイルストーン

Shapez2 in Lean (S2IL) プロジェクトの最終目標・大きな方針・層別の実行計画をまとめた入口ページ。

新しい証明に着手する前や、既存計画を見直すときにまずここを参照する。

---

## ファイル一覧

### プロジェクト全体の目標

| ファイル | 概要 |
|---|---|
| [MILESTONES.md](MILESTONES.md) | MAM 完全性に至る最終目標と、Data / Behavior / Flow / MAM の層構造 |

### 確立済みアーキテクチャ資料

| ファイル | 概要 |
|---|---|
| [../s2il/architecture-layer-ab.md](../s2il/architecture-layer-ab.md) | Layer A/B のディレクトリ構造・設計原則・主要 theorem チェーンの正本 |

### Layer B 追加証明計画

| ファイル | 概要 |
|---|---|
| [layer-b-mam-prereq-proof-plan.md](layer-b-mam-prereq-proof-plan.md) | `mam.md` §4-1〜§4-4 / §5 の精査に基づく、象限抽出・積層正しさの追加証明計画 |

### Layer C 実行計画

| ファイル | 概要 |
|---|---|
| [layer-c1-shape-processing-flow-plan.md](layer-c1-shape-processing-flow-plan.md) | Layer C-1 Shape Processing Flow の加工ライン、ベルト / パイプのストリーム、抽象処理能力の設計・実装計画 |

---

## いつ参照するか

| 作業 | 参照先 |
|---|---|
| プロジェクト全体の位置付けを確認 | `MILESTONES.md` |
| Layer C-1 の Flow 設計に着手 | `layer-c1-shape-processing-flow-plan.md` |
| Layer A/B の構造原則を確認 | `../s2il/architecture-layer-ab.md` |
| 個別 sorry の現状を確認 | `../../S2IL/_agent/sorry-plan.json` / `../../S2IL/_agent/sorry-goals.md` |
| 新しい証明計画を策定する | `../agent/proof-plan-current-focus-guide.md` |

## 新規ファイルの追加基準

- **追加する**: 新たな層の再構築計画や、大規模な証明調査が必要な場合
- **追加しない**: 小規模な証明（1〜2 sorry 程度）は `docs/s2il/` に知見として記録する
- **ファイル名**: 対象をケバブケースで（例: `stacker-equivariance-proof-plan.md`）
- 新規ファイルを追加したらこの README の一覧にも追記する
