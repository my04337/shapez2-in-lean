# S2IL/Operations/Settled/Core.lean

- Lines: 122
- Declarations: 4 (theorems/lemmas: 4, defs/abbrev: 0, private: 3, sorry: 0)

## Landmarks

L6     namespace Shape

## Declarations

```
L13    theorem    Shape.groundingEdge_normalize_mono[priv] : (s s' : Shape) (h_norm : s.normalize = some s') (a b : QuarterPos) (h : Gravity.groundingEdge s a b = true) : Gravity.groundingEdge s' a b = true
L29    theorem    Shape.groundedPositions_normalize_mono[priv] : (s s' : Shape) (h_norm : s.normalize = some s') (p : QuarterPos) (h_grounded : p ∈ Gravity.groundedPositions s) : p ∈ Gravity.groundedPositions s'
L74    theorem    Shape.floatingUnits_nil_of_normalize[priv] : (s : Shape) (s' : Shape) (h_norm : s.normalize = some s') (h_nil : Gravity.floatingUnits s = []) : Gravity.floatingUnits s' = []
L115   theorem    Shape.IsSettled_normalize : (s : Shape) (s' : Shape) (h_norm : s.normalize = some s') (h_settled : s.IsSettled) : s'.IsSettled
```
