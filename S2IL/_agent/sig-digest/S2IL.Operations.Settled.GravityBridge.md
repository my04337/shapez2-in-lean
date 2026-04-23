# S2IL/Operations/Settled/GravityBridge.lean

- Lines: 29
- Declarations: 1 (theorems/lemmas: 1, defs/abbrev: 0, private: 0, sorry: 0)

## Landmarks

L7     namespace Shape

## Declarations

```
L20    theorem    Shape.gravity_IsSettled : (s : Shape) (s' : Shape) (h : s.gravity = some s') (_h_lc : s.layerCount ≤ 5) : s'.IsSettled
```
