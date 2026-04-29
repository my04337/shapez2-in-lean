# Sorry Goals Snapshot

> 自動生成: 2026-04-29 19:51:03
> ソース: `.lean` ファイル直接スキャン (build diagnostics に非依存)
> スキャン対象: S2IL
> 用途: sorry 位置の含む宣言シグネチャを REPL 起動なしで取得する

sorry 件数: **7**

## 1. S2IL/Operations/Gravity/Internal/Collision.lean:336

- 宣言: `isGrounded_of_isGroundedFast` (*theorem* at L327)

```lean
theorem isGrounded_of_isGroundedFast
    (s : Shape) (p : QuarterPos) :
    isGroundedFast s p = true → IsGrounded s p := by
```

sorry 行: `sorry`

## 2. S2IL/Operations/Gravity/Internal/Collision.lean:347

- 宣言: `isGroundedFast_of_isGrounded` (*theorem* at L339)

```lean
theorem isGroundedFast_of_isGrounded
    (s : Shape) (p : QuarterPos) :
    IsGrounded s p → isGroundedFast s p = true := by
```

sorry 行: `sorry`

## 3. S2IL/Operations/Gravity/Internal/Collision.lean:376

- 宣言: `structuralCluster_canFormBond` (*theorem* at L365)

```lean
theorem structuralCluster_canFormBond
    (s : Shape) (p q : QuarterPos)
    (hq : q ∈ structuralCluster s p) :
    (QuarterPos.getQuarter s q).canFormBond = true := by
```

sorry 行: `sorry`

## 4. S2IL/Operations/Gravity/Internal/Collision.lean:388

- 宣言: `structuralCluster_nonEmpty` (*theorem* at L379)

```lean
theorem structuralCluster_nonEmpty
    (s : Shape) (p q : QuarterPos)
    (hq : q ∈ structuralCluster s p) :
    ¬ (QuarterPos.getQuarter s q).isEmpty := by
```

sorry 行: `sorry`

## 5. S2IL/Operations/Gravity/Internal/Collision.lean:404

- 宣言: `floatingClusters_eq_nil_of_isSettled` (*theorem* at L395)

```lean
theorem floatingClusters_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingClusters s = [] := by
```

sorry 行: `sorry`

## 6. S2IL/Operations/Gravity/Internal/Collision.lean:415

- 宣言: `floatingPins_eq_nil_of_isSettled` (*theorem* at L407)

```lean
theorem floatingPins_eq_nil_of_isSettled
    {s : Shape} (hs : IsSettled s) :
    floatingPins s = [] := by
```

sorry 行: `sorry`

## 7. S2IL/Operations/Gravity/Internal/Collision.lean:453

- 宣言: `gravity_isSettled_collision` (*theorem* at L433)

```lean
theorem gravity_isSettled_collision (s : Shape) :
    IsSettled (Shape.gravity s) := by
```

sorry 行: `sorry`

