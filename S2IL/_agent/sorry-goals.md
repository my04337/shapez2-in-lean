# Sorry Goals Snapshot

> 自動生成: 2026-04-29 23:05:21
> ソース: `.lean` ファイル直接スキャン (build diagnostics に非依存)
> スキャン対象: S2IL
> 用途: sorry 位置の含む宣言シグネチャを REPL 起動なしで取得する

sorry 件数: **4**

## 1. S2IL/Operations/Gravity/Internal/Settled.lean:475

- 宣言: `placeUnit_grounding` (*theorem* at L461)

```lean
private theorem placeUnit_grounding
    (origS acc : Shape) (u : FallingUnit) (d : Nat)
    (_hLand : landingCondition acc u d = true)
    (_hAcc  : ∀ q : QuarterPos, q ∈ QuarterPos.allValid acc →
              ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q)
    {p : QuarterPos} (_hp : p ∈ u.positions) :
    IsGrounded (placeUnit origS acc u d) (p.1 - d, p.2) := by
```

sorry 行: `sorry`

## 2. S2IL/Operations/Gravity/Internal/Settled.lean:495

- 宣言: `foldl_grounded_invariant` (*theorem* at L478)

```lean
private theorem foldl_grounded_invariant
    (s : Shape) (units : List FallingUnit)
    (acc : Shape)
    (_hBase : ∀ q ∈ QuarterPos.allValid acc,
              ¬ (QuarterPos.getQuarter acc q).isEmpty → IsGrounded acc q) :
    let result := units.foldl (fun a u => stepUnit s a u) acc
```

sorry 行: `sorry`

## 3. S2IL/Operations/Gravity/Internal/Settled.lean:521

- 宣言: `obs0_isGrounded_of_nonEmpty` (*theorem* at L507)

```lean
private theorem obs0_isGrounded_of_nonEmpty
    (s : Shape) :
    let units := floatingUnits s
```

sorry 行: `sorry`

## 4. S2IL/Operations/Gravity/Internal/Settled.lean:539

- 宣言: `gravity_isSettled_collision` (*theorem* at L526)

```lean
theorem gravity_isSettled_collision (s : Shape) :
    IsSettled (Shape.gravity s) := by
```

sorry 行: `sorry`

