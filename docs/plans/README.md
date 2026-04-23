# 計画・マイルストーン

Shapez2 in Lean (S2IL) プロジェクトの最終目標・大きな方針・層別の実行計画をまとめた入口ページ。

新しい証明に着手する前や、既存計画を見直すときにまずここを参照する。

---

## ファイル一覧

### プロジェクト全体の目標

| ファイル | 概要 |
|---|---|
| [MILESTONES.md](MILESTONES.md) | MAM 完全性に至る最終目標と、Data / Behavior / Flow / MAM の層構造 |

### 層別の実行計画

| ファイル | 概要 |
|---|---|
| [gravity-greenfield-rewrite-plan.md](gravity-greenfield-rewrite-plan.md) | Layer B（落下・結晶砕け散り・安定化）の再構築計画。CW 等変性への一本化と重複排除 |

---

## いつ参照するか

| 作業 | 参照先 |
|---|---|
| プロジェクト全体の位置付けを確認 | `MILESTONES.md` |
| Gravity 層の構造を変更する | `gravity-greenfield-rewrite-plan.md` |
| 個別 sorry の現状を確認 | `../../S2IL/_agent/sorry-plan.json` / `../../S2IL/_agent/sorry-goals.md` |
| 新しい証明計画を策定する | `../agent/proof-plan-current-focus-guide.md` |

## 新規ファイルの追加基準

- **追加する**: 新たな層の再構築計画や、大規模な証明調査が必要な場合
- **追加しない**: 小規模な証明（1〜2 sorry 程度）は `docs/s2il/` に知見として記録する
- **ファイル名**: 対象をケバブケースで（例: `stacker-equivariance-proof-plan.md`）
- 新規ファイルを追加したらこの README の一覧にも追記する
