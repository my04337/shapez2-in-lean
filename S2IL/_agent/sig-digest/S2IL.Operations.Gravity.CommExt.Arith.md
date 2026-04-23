# S2IL/Operations/Gravity/CommExt/Arith.lean

- Lines: 105
- Declarations: 5 (theorems/lemmas: 5, defs/abbrev: 0, private: 2, sorry: 0)

## Landmarks

L6     header    # Gravity CommExt: 着地合計の telescoping（arithmetic）
L16    namespace Gravity

## Declarations

```
L23    theorem    Gravity.sum_map_layer_landing_telescope : (ps : List QuarterPos) (d : Nat) (h_ge : ∀ p ∈ ps, d ≤ p.layer) : (ps.map fun p => (p.layer - d) + 1).sum + ps.length * d = (ps.map fun p => p.layer + 1).sum
L36    theorem    Gravity.sublist_sum_le_sum_nat[priv] : {l1 l2 : List Nat} (h : l1.Sublist l2) : l1.sum ≤ l2.sum
L49    theorem    Gravity.landing_sum_bound : (ps : List QuarterPos) (pred : QuarterPos → Bool) (d : Nat) (hd : 1 ≤ d) (h_ge : ∀ p ∈ ps, d ≤ p.layer) (h_ne : ps ≠ []) : ((ps.filter pred).map fun p => (p.layer - d) + 1...
L67    theorem    Gravity.sum_map_le_of_pointwise_nat[priv] : {α : Type*} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum
L86    theorem    Gravity.landing_sum_bound_var_d : (ps : List QuarterPos) (pred : QuarterPos → Bool) (actual_d : QuarterPos → Nat) (h_pos : ∀ p ∈ ps, 1 ≤ actual_d p) (h_le_layer : ∀ p ∈ ps, 1 ≤ p.layer) (h_ne : ps ≠ ...
```
