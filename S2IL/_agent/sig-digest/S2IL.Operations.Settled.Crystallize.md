# S2IL/Operations/Settled/Crystallize.lean

- Lines: 125
- Declarations: 10 (theorems/lemmas: 10, defs/abbrev: 0, private: 8, sorry: 0)

## Landmarks

L10    namespace Gravity
L114   namespace Shape

## Declarations

```
L13    theorem    Gravity.fillQuarter_not_isEmpty[priv] : (q : Quarter) (c : Color) : (CrystalGenerator.fillQuarter q c).isEmpty = false
L18    theorem    Gravity.getDir_fillLayer[priv] : (l : Layer) (d : Direction) (c : Color) : QuarterPos.getDir (CrystalGenerator.fillLayer l c) d = CrystalGenerator.fillQuarter (QuarterPos.getDir l d) c
L24    theorem    Gravity.layerCount_crystallize[priv] : (s : Shape) (c : Color) : (s.crystallize c).layerCount = s.layerCount
L29    theorem    Gravity.getQuarter_crystallize[priv] : (s : Shape) (pos : QuarterPos) (c : Color) (h : pos.layer < s.layerCount) : pos.getQuarter (s.crystallize c) = some (CrystalGenerator.fillQuarter (QuarterPos....
L42    theorem    Gravity.isGroundingContact_crystallize_vertical[priv] : (s : Shape) (c : Color) (d : Direction) (k : Nat) (hk : k + 1 < s.layerCount) : isGroundingContact (s.crystallize c) ⟨k, d⟩ ⟨k + 1, d⟩ = true
L56    theorem    Gravity.reachable_from_zero_crystallize[priv] : (s : Shape) (c : Color) (d : Direction) (i : Nat) (hi : i < s.layerCount) : GenericReachable (isUpwardGroundingContact (s.crystallize c)) ⟨0, d⟩ ⟨i, d⟩
L69    theorem    Gravity.seed_valid_crystallize[priv] : (s : Shape) (c : Color) (d : Direction) (h : 0 < s.layerCount) : ⟨0, d⟩ ∈ (QuarterPos.allValid (s.crystallize c)).filter (fun q => q.layer == 0 && match q.get...
L85    theorem    Gravity.all_grounded_crystallize[priv] : (s : Shape) (c : Color) (p : QuarterPos) (hp : p.layer < s.layerCount) : p ∈ groundedPositions (s.crystallize c)
L98    theorem    Gravity.floatingUnits_crystallize_eq : (s : Shape) (c : Color) : floatingUnits (s.crystallize c) = []
L118   theorem    Shape.IsSettled_crystallize : (s : Shape) (c : Color) : (s.crystallize c).IsSettled
```
