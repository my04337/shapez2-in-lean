# 次セッション指示書（Phase D-10D-5e 着手 / 2026-04-29）

## 1. 開始時にやること

1. `lean-session-restorer` を呼び出す
2. [docs/plans/gravity-proof-plan.md](../docs/plans/gravity-proof-plan.md) §4 D-10D-5 サブテーブルを確認
3. `lake build` で green / sorry 4 / axiom 24 を再確認

## 2. 現状サマリ（D-10D-5d 完了直後）

- ステータス: Phase D-10D-5d 完了 + R-§6.4 反例検証完了
- ビルド: green、0 errors / **3 warnings (push_neg ×2 + 未使用 simp 引数 ×1)** / **4 sorries** / axiom **24** 不変

### 完了した補題（このセッション）

- ✅ **D-10D-5c** `landingCondition_landingDistance_pos`
  - `Option.isSome_iff_exists` + `List.find?_some` + `landingDistance` unfold + `simp [hd]` で `getD m` を `d` に簡約
- ✅ **D-10D-5d** `placeUnit_subsumed_by`（条件付き、`hDisjoint` 仮定下）
  - §6.4 冒頭に基本性質補題を 4 本集約:
    - `length_setQuarter` / `getQuarter_setQuarter_of_ne`（同レイヤ別方向 + 別レイヤ）
    - `foldl_setQuarter_length` / `foldl_setQuarter_getQuarter_of_not_target`
  - 本体は subsumed_by を 2 成分に分解 (length 不変 / getQuarter 不変)
- ✅ **R-§6.4 反例検証** [Scratch/PhaseD10D_PlaceUnit_Disjoint.lean](PhaseD10D_PlaceUnit_Disjoint.lean)
  - §4.1 / §4.1.1 11 例 + interlock I-1 / I-1' / I-2 / I-3 + 追加 8 例 = **23 ケース** 全て OK
  - foldl 中間 `acc'` ごとに `∀ p ∈ u.positions, (getQuarter acc' (p.1 - landingDistance acc' u, p.2)).isEmpty` を `#eval` 検査
  - **Gravity モデル再設計は不要**（pivot 棚上げ、観点はリスクレジスタに保存）

### 残 sorry 4 本（すべて [S2IL/Operations/Gravity/Internal/Settled.lean](../S2IL/Operations/Gravity/Internal/Settled.lean)）

| # | 補題 | 行 | サブ |
|---|---|---|---|
| 1 | `placeUnit_grounding` | L461 | D-10D-5e |
| 2 | `foldl_grounded_invariant` | L478 | D-10D-5f |
| 3 | `obs0_isGrounded_of_nonEmpty` | L507 | D-10D-5g 基底 |
| 4 | `gravity_isSettled_collision` | L526 | D-10D-5g 主定理 |

## 3. 次セッションのゴール

**D-10D-5e** (`placeUnit_grounding`) を最優先で攻略する。本フェーズの **核心**。

### D-10D-5e 戦略（要 unit 内連結性補題）

ゴール: `IsGrounded (placeUnit origS acc u d) (p.1 - d, p.2)` (任意 `p ∈ u.positions`)

1. `landingCondition acc u d = true` を `List.any_eq_true` + `decide` で展開
   ⇒ `∃ q ∈ u.positions, q.1 = d ∨ (q.1 > d ∧ getQuarter acc (q.1 - d - 1, q.2) ≠ empty)`
2. ケース分岐:
   - **layer 0 ケース** (`q.1 = d`): 着地像 `q' = (q.1 - d, q.2) = (0, q.2)` ⇒ `q'` 自身が root
   - **直下障害物ケース**: `obstacle = (q.1 - d - 1, q.2)` は acc で非空 ⇒ `hAcc` で `IsGrounded acc obstacle` ⇒ `IsGrounded.mono` で `IsGrounded (placeUnit ...) obstacle` ⇒ obstacle から `q'` へ `IsGroundingEdge.IsUpwardGroundingContact` (vertical, +1) で接地経路延長
3. **要・新規補題: `unit_path_from_to`** — unit `u` 内で任意の 2 点 `q, p ∈ u.positions` の着地像が `IsGroundingEdge` で連結:
   - cluster ケース: structuralCluster の bond で接続 (cross-layer の場合は IsBondedCrossLayer / 同層は IsBondedInLayer)
   - pin ケース: 単点 unit なので `q = p`、自明
4. ↑ で `(q.1-d, q.2)` から `(p.1-d, p.2)` まで `ReflTransGen (IsGroundingEdge result)` ⇒ `IsGrounded result (p.1-d, p.2)`

### 必要そうな前提補題

- `setQuarter` 後の `IsGroundingEdge` 保存（`subsumed_by` 経由 or 直接）
- unit 内 bond 連結性: `FallingUnit.cluster cl` で `cl` が `structuralCluster` ⇒ クラスタ内任意 2 点が `IsBonded` の `ReflTransGen` で連結
- `placeUnit` で書込まれた cell の値 = `quarterAt origS p`（特に `IsCrystal` 性が origS から保存される）

### REPL 先行確認

`example` 形でゴール展開を確認し、unit 内 path 補題の signature を確定してから本体に入る。
特に「cluster の structural connectivity ⇒ 任意 2 点 ReflTransGen 接続」は要 REPL 確認。

## 4. 撤退条件（plan 既定）

- 3 セッション連続で同一補題が閉じない、または 8 アプローチ失敗
- D-10D-5e で unit 内連結性が `structuralCluster` の現行定義から取れない反例発見

## 5. 衛生改善（低優先）

- `Internal/Settled.lean` L170 / L220 の `push_neg` を `push Not` に置換（deprecation 警告 2 件）
- L401 の `simp [hq, hq'']` の linter 警告（hq が未使用と誤認）— `set_option linter.unusedSimpArgs false in` で抑制 or 別証法に書換

## 6. 参考

- 計画: [docs/plans/gravity-proof-plan.md](../docs/plans/gravity-proof-plan.md) §4 D-10D-5 サブテーブル
- 主要ソース:
  - [S2IL/Operations/Gravity/Internal/Settled.lean](../S2IL/Operations/Gravity/Internal/Settled.lean) §6.4〜§6.6
  - [S2IL/Operations/Gravity/Internal/Collision.lean](../S2IL/Operations/Gravity/Internal/Collision.lean) §1〜§5
  - [S2IL/Operations/Gravity/Defs.lean](../S2IL/Operations/Gravity/Defs.lean)（`landingCondition` / `landingDistance` / `placeUnit` / `stepUnit`）
  - [S2IL/Kernel/Bond.lean](../S2IL/Kernel/Bond.lean)（`IsBondedInLayer` / `IsBondedCrossLayer`）
  - [S2IL/Kernel/Cluster.lean](../S2IL/Kernel/Cluster.lean)（`structuralCluster` 連結性）
- 反例検証:
  - [Scratch/PhaseD10D_PlaceUnit_Disjoint.lean](PhaseD10D_PlaceUnit_Disjoint.lean) (R-§6.4 検証済)
  - [Scratch/PhaseD10B_GravityCheck.lean](PhaseD10B_GravityCheck.lean) / [Scratch/PhaseD10C_BehaviorCheck.lean](PhaseD10C_BehaviorCheck.lean)
- repo memory: `counterexample-layer-benchmark.md` / `lean-getelem-rewrite-motive.md` / `lean-proof-tips.md` / `repl-quick-checklist.md`
