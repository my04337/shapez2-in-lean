# 次セッション指示書（Phase D-10D-5j 着手 / 2026-04-29）

## 1. 開始時にやること

1. `lean-session-restorer` を呼び出す
2. [docs/plans/gravity-proof-plan.md](../docs/plans/gravity-proof-plan.md) §4 D-10D-5 サブテーブルを確認
3. `lake build` で green / sorry 5 / axiom 24 を再確認

## 2. 現状サマリ（D-10D-5i 完了直後）

- ステータス: Phase D-10D-5i 完了（§6.6.F lift 解消）
- ビルド: green、0 errors / **1 warning (未使用 simp 引数 ×1)** / **5 sorries** / axiom **24** 不変

### 完了した補題（このセッション）

- ✅ **D-10D-5i** §6.6.F `obs0_isGrounded_of_nonEmpty` 最終 lift
  - 新 helper `IsGroundingEdge.of_getQuarter_eq`（両端 `getQuarter` 値一致 ⇒ edge 保存、§6.6 冒頭）
  - 本体: B (obs0 非空 ⇒ s 値一致) + D (s で IsGrounded) で root 取得 ⇒ E (`grounded_path_avoids_floating`) を path 部分長 `hPath_ab` / `hPath_ab.tail hedge` に適用 ⇒ 両端が floating unit 外 ⇒ `clearPositions_getQuarter_of_not_in` で値不変 ⇒ helper で edge を obs0 へ lift ⇒ ReflTransGen 帰納で path lift
- ✅ **衛生**: `push_neg` の deprecation 警告 3 件を `push Not` に一括置換
  - L170 `normalize_length_of_nonEmpty` / L220 `nonEmpty_imp_layer_lt` / L463 `foldl_setQuarter_const_empty_at_in_target`

### 残 sorry 5 本（すべて [S2IL/Operations/Gravity/Internal/Settled.lean](../S2IL/Operations/Gravity/Internal/Settled.lean)）

| # | 補題 | 行 | サブ | 性質 |
|---|---|---|---|---|
| 1 | `placeUnit_witness_grounded` | L556 | 5e-B | `placeUnit_writes_origS_value` 1 補助 |
| 2 | `placeUnit_unit_internal_path` | L580 | 5e-C | unit 構造結合の `placeUnit` 持ち上げ |
| 3 | `stepUnit_landing_disjoint` | L638 | 5f-A | **R-§6.4 中核**、反例検証済 |
| 4 | `stepUnit_grounded_invariant_step` | L669 | 5f-C | 5f-A 完成後 wiring |
| 5 | `not_floating_imp_grounded` | L791 | 5g-D | pin 直 / cluster は連結性 helper 必要 |

## 3. 次セッションのゴール（推奨優先順位）

### 第 1 候補: **5g-D `not_floating_imp_grounded`**（中難度、§6.6 完了の最後の 1 ピース）

ゴール: `q ∈ allValid s` ∧ `¬ (getQuarter s q).isEmpty` ∧ `∀ u ∈ floatingUnits s, q ∉ u.positions` ⇒ `IsGrounded s q`

#### 戦略

1. **pin ケース** (`getQuarter s q = Quarter.pin`):
   - `floatingPins s = filter (pin && !isGroundedFast) (nonEmptyPositions s)`
   - `q ∉ floatingPins s` ∧ q は pin かつ非空 ⇒ filter 述語の右側 `!isGroundedFast` が false ⇒ `isGroundedFast s q = true`
   - `isGroundedFast_iff_isGrounded` で `IsGrounded s q`
2. **bondable ケース** (`getQuarter s q ≠ pin` ∧ ¬ empty ⇒ `canFormBond = true`):
   - q ∈ bondablePos ⇒ ∃ cl ∈ structuralClusters s, q ∈ cl
   - `q ∉ FallingUnit.cluster cl` ⇒ cl ∉ floatingClusters ⇒ `clusterFloating s cl = false`
   - `clusterFloating` は `cl.all (! isGroundedFast)` なので false ⇒ ∃ p ∈ cl, isGroundedFast s p = true
   - cluster 連結性で q も grounded

#### 必要な helper（新規 2 本）

```lean
-- 6.6.D-1: bondable な非空セルは構造クラスタ partition のいずれかに含まれる
private theorem mem_structuralClusters_of_canFormBond
    (s : Shape) {q : QuarterPos}
    (hValid : q ∈ QuarterPos.allValid s)
    (hne : ¬ (QuarterPos.getQuarter s q).isEmpty)
    (hbond : (QuarterPos.getQuarter s q).canFormBond = true) :
    ∃ cl ∈ structuralClusters s, q ∈ cl

-- 6.6.D-2: 構造クラスタ内では isGroundedFast が一様
private theorem structuralCluster_grounded_uniform
    (s : Shape) {cl : List QuarterPos} (hcl : cl ∈ structuralClusters s)
    {p q : QuarterPos} (hp : p ∈ cl) (hq : q ∈ cl)
    (hfast : isGroundedFast s p = true) :
    isGroundedFast s q = true
```

D-2 の根拠: cl の任意 2 点は `structuralNeighbors` 連鎖で結ばれる（BFS reachClosure の特徴付け）。各 `structuralNeighbors` は IsBonded ⇒ IsGroundingEdge（双方向）⇒ BFS forward 到達性が cluster 内で同値類化。

D-1 の根拠: `structuralClustersPartition` は bondablePos を全射的に分割（fuel 充足下）。`structuralCluster s p` には p 自身が必ず含まれる（`mem_init_subset_reachClosure`、既存）。

#### REPL 先行確認

partition の全射性（fuel 充足版）と `structuralNeighbors` の対称性を REPL で先に確認する:

```text
{"cmd":"import S2IL\nopen S2IL\n#check @structuralClustersPartition\n#check @structuralCluster\n#check @Internal.mem_structuralClustersPartition\nexample (s : Shape) (p q : QuarterPos) (h : q ∈ structuralNeighbors s p) :\n    p ∈ structuralNeighbors s q := by sorry"}
```

`structuralNeighbors` の対称性が定義から自明か（双方向探索か forward のみか）の確認が必須。forward のみなら BFS 双方向化または対称化補助が要。

### 第 2 候補: **5e-B `placeUnit_witness_grounded`**（中難度）

5g-D を後回しにする場合。要 helper 1 本:

```lean
private theorem placeUnit_writes_origS_value
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    {p : QuarterPos} (hp : p ∈ u.positions)
    (hUniqueLanding : ∀ q ∈ u.positions, q ≠ p →
      ((q.1 - d, q.2) : QuarterPos) ≠ (p.1 - d, p.2)) :
    QuarterPos.getQuarter (placeUnit origS acc u d) (p.1 - d, p.2)
      = QuarterPos.getQuarter origS p
```

`hUniqueLanding` の根拠: cluster は構造クラスタとして互いに異なる QuarterPos の集合、shift `(p.1-d, p.2)` の単射性は `(p.1, p.2) ↦ (p.1-d, p.2)` が p.1 ≥ d かつ自然数 sub ⇒ 同位置帰着 ⇒ 元位置同じ。pin は単位リストなので自明。

### 第 3 候補: **5f-A `stepUnit_landing_disjoint`**（**R-§6.4 中核、最大山場**）

23 ケース反例検証済で真。証明戦略は plan §4 / §5 リスクレジスタ参照。`hAccBound` の inductive 不変量を充分強化（acc の各非空セルが s で grounded、acc.subsumed_by s に近い性質）すれば閉じる見込み。

## 4. 撤退条件（plan 既定）

- 3 セッション連続で同一補題が閉じない、または 8 アプローチ失敗
- 5g-D で structuralCluster の連結性が現行 BFS 定義から取れない反例発見（特に `structuralNeighbors` が forward only で対称化されていない場合）

## 5. 衛生改善（低優先）

- L401 `getQuarter_setQuarter_of_ne` の `simp [hq, hq'']` 未使用 simp 引数警告 1 件 — `simp [hq'']` だと壊れる（依存的）。`set_option linter.unusedSimpArgs false in` で抑制 or 別証法に書換するのは別タイミングで。

## 6. 参考

- 計画: [docs/plans/gravity-proof-plan.md](../docs/plans/gravity-proof-plan.md) §4 D-10D-5 サブテーブル
- 主要ソース:
  - [S2IL/Operations/Gravity/Internal/Settled.lean](../S2IL/Operations/Gravity/Internal/Settled.lean) §6.4〜§6.6
  - [S2IL/Operations/Gravity/Internal/Collision.lean](../S2IL/Operations/Gravity/Internal/Collision.lean) §1〜§5（structuralCluster 構造不変補題群）
  - [S2IL/Operations/Gravity/Defs.lean](../S2IL/Operations/Gravity/Defs.lean)（`structuralClustersPartition` / `floatingPins` / `floatingClusters` / `landingCondition` / `placeUnit`）
  - [S2IL/Kernel/Bond.lean](../S2IL/Kernel/Bond.lean)（`IsBonded` symm 群）
- 反例検証:
  - [Scratch/PhaseD10D_PlaceUnit_Disjoint.lean](PhaseD10D_PlaceUnit_Disjoint.lean) (R-§6.4 検証済)
- repo memory: `counterexample-layer-benchmark.md` / `lean-getelem-rewrite-motive.md` / `lean-proof-tips.md` / `repl-quick-checklist.md`

## 7. 反例で Gravity モデル再設計が必要になった場合の観点

5g-D / 5f-A で反例発覚時の **新モデル設計指針**（gravity-proof-plan.md §5 リスクレジスタ R-§6.4 の補完）:

- **R-§6.4 (5f-A)**: 既に 23 ケース反例検証済で真の見込み。それでも成立しないなら `landingCondition` 強化（全着地像セル空仮定）か `dropOf` 静的化（s 固定）。
- **structuralCluster 連結性 (5g-D)**: もし「クラスタ内に grounded セルあり ⇒ 全 grounded」が破れる反例（特に cross-layer cluster で片側のみ layer 0 root と接続するケース）が見つかれば、`isGroundedFast` の BFS forward direction が cluster で対称でない可能性。`structuralNeighbors` の対称性確認（双方向走査か）が要点。対称化されていなければ BFS を双方向化（reachable in both directions）する代替 def を検討。
- **bondable 全射性 (5g-D)**: もし `structuralClustersPartition` が fuel 不足で一部 bondable セルを取りこぼす反例があれば、fuel 値を `s.length * 4 + bondablePos.length` 等に強化する。ただし fuel = `s.length * 4 + 4` は spec §6.5 で許容される最大 cluster 直径より十分大きいので、現実的には起こらない見込み。

新モデル候補（pivot 時）:

1. **着地条件強化** `landingCondition'`: `∧ u.positions.all (fun p => (getQuarter obs (p.1-d, p.2)).isEmpty)`
2. **完全宣言的モデル (b)**: `gravity := Classical.choose ...` + `gravity_spec` 一意性
3. **dropOf 静的化**: `dropOf u s : Nat`（acc 非依存、well-founded 再帰）
4. **位置写像純粋化**: foldl `setQuarter` ではなく `Shape.fromMap` 風宣言的構成
5. **structuralNeighbors 双方向化**: 現行は forward + backward のどちらか不明、双方向化で対称化
