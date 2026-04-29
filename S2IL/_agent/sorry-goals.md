# Sorry Goals Snapshot

> 自動生成: 2026-04-30 00:02:24
> ソース: `.lean` ファイル直接スキャン (build diagnostics に非依存)
> スキャン対象: S2IL
> 用途: sorry 位置の含む宣言シグネチャを REPL 起動なしで取得する

sorry 件数: **5**

## 1. S2IL/Operations/Gravity/Internal/Settled.lean:567

- 宣言: `placeUnit_witness_grounded` (*theorem* at L556)

```lean
private theorem placeUnit_witness_grounded
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    (_hAcc : ∀ q : QuarterPos, q ∈ QuarterPos.allValid acc →
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (_hDisjoint : ∀ p ∈ u.positions, ∀ q : QuarterPos,
        q = (p.1 - d, p.2) → (QuarterPos.getQuarter acc q).isEmpty)
    (_hOrigS : ∀ p ∈ u.positions, ¬ (QuarterPos.getQuarter origS p).isEmpty)
    {q : QuarterPos} (_hq_in : q ∈ u.positions)
    (_hq_pred : q.1 = d ∨ (q.1 > d ∧
      ¬ (QuarterPos.getQuarter acc (q.1 - d - 1, q.2)).isEmpty)) :
    IsGrounded (placeUnit origS acc u d) (q.1 - d, q.2) := by
```

sorry 行: `sorry`

## 2. S2IL/Operations/Gravity/Internal/Settled.lean:585

- 宣言: `placeUnit_unit_internal_path` (*theorem* at L580)

```lean
private theorem placeUnit_unit_internal_path
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    {p q : QuarterPos} (_hp : p ∈ u.positions) (_hq : q ∈ u.positions) :
    Relation.ReflTransGen (IsGroundingEdge (placeUnit origS acc u d))
      (q.1 - d, q.2) (p.1 - d, p.2) := by
```

sorry 行: `sorry`

## 3. S2IL/Operations/Gravity/Internal/Settled.lean:647

- 宣言: `stepUnit_landing_disjoint` (*theorem* at L638)

```lean
private theorem stepUnit_landing_disjoint
    (s acc : Shape) (u : FallingUnit)
    (_hAcc : ∀ q ∈ QuarterPos.allValid acc,
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (_hUnit : u ∈ floatingUnits s)
    (_hAccBound : Shape.subsumed_by acc s ∨ acc.length = s.length) :
    let d := landingDistance acc u
```

sorry 行: `sorry`

## 4. S2IL/Operations/Gravity/Internal/Settled.lean:679

- 宣言: `stepUnit_grounded_invariant_step` (*theorem* at L669)

```lean
private theorem stepUnit_grounded_invariant_step
    (s acc : Shape) (u : FallingUnit)
    (_hAcc : ∀ q ∈ QuarterPos.allValid acc,
             ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    (_hUnit : u ∈ floatingUnits s)
    (_hAccBound : Shape.subsumed_by acc s ∨ acc.length = s.length) :
    let acc' := stepUnit s acc u
```

sorry 行: `sorry`

## 5. S2IL/Operations/Gravity/Internal/Settled.lean:797

- 宣言: `not_floating_imp_grounded` (*theorem* at L791)

```lean
private theorem not_floating_imp_grounded
    (s : Shape) {q : QuarterPos}
    (_hValid : q ∈ QuarterPos.allValid s)
    (_hne : ¬ (QuarterPos.getQuarter s q).isEmpty)
    (_hnf : ∀ u ∈ floatingUnits s, q ∉ u.positions) :
    IsGrounded s q := by
```

sorry 行: `sorry`

