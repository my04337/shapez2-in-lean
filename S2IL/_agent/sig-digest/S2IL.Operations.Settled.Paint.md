# S2IL/Operations/Settled/Paint.lean

- Lines: 311
- Declarations: 24 (theorems/lemmas: 24, defs/abbrev: 0, private: 22, sorry: 0)

## Landmarks

L9     header    # SettledState (安定状態の保存)
L81    namespace Gravity
L301   namespace Shape

## Declarations

```
L29    theorem    getElem?_dropLast_append_last[priv] : {α : Type} (l : List α) (_h_ne : l ≠ []) (y : α) : (l.dropLast ++ [y])[l.length - 1]? = some y
L36    theorem    getElem?_dropLast_append_other[priv] : {α : Type} (l : List α) (h_ne : l ≠ []) (y : α) (i : Nat) (h_ne_idx : i ≠ l.length - 1) : (l.dropLast ++ [y])[i]? = l[i]?
L56    theorem    isPin_some[priv] : (q : Quarter) : (match (some q : Option Quarter) with | some .pin => true | _ => false) = (match q with | .pin => true | _ => false)
L62    theorem    paintQuarter_canFormBond[priv] : (q : Quarter) (c : Color) : (Painter.paintQuarter q c).canFormBond = q.canFormBond
L67    theorem    paintQuarter_isEmpty[priv] : (q : Quarter) (c : Color) : (Painter.paintQuarter q c).isEmpty = q.isEmpty
L72    theorem    paintQuarter_pin_match[priv] : (q : Quarter) (c : Color) : (match Painter.paintQuarter q c with | .pin => true | _ => false) = (match q with | .pin => true | _ => false)
L84    theorem    Gravity.getDir_paintLayer_canFormBond[priv] : (l : Layer) (c : Color) (d : Direction) : (QuarterPos.getDir (Painter.paintLayer l c) d).canFormBond = (QuarterPos.getDir l d).canFormBond
L90    theorem    Gravity.getDir_paintLayer_isEmpty[priv] : (l : Layer) (c : Color) (d : Direction) : (QuarterPos.getDir (Painter.paintLayer l c) d).isEmpty = (QuarterPos.getDir l d).isEmpty
L96    theorem    Gravity.getDir_paintLayer_pin_match[priv] : (l : Layer) (c : Color) (d : Direction) : (match QuarterPos.getDir (Painter.paintLayer l c) d with | .pin => true | _ => false) = (match QuarterPos.getDi...
L102   theorem    Gravity.getQuarter_paint_canFormBond[priv] : (s : Shape) (c : Color) (p : QuarterPos) : (p.getQuarter (s.paint c)).map Quarter.canFormBond = (p.getQuarter s).map Quarter.canFormBond
L119   theorem    Gravity.getQuarter_paint_isEmpty[priv] : (s : Shape) (c : Color) (p : QuarterPos) : (p.getQuarter (s.paint c)).map Quarter.isEmpty = (p.getQuarter s).map Quarter.isEmpty
L134   theorem    Gravity.getQuarter_paint_isPin[priv] : (s : Shape) (c : Color) (p : QuarterPos) : (match p.getQuarter (s.paint c) with | some .pin => true | _ => false) = (match p.getQuarter s with | some .pin => ...
L149   theorem    Gravity.getQuarter_paint_none[priv] : (s : Shape) (c : Color) (p : QuarterPos) (h : p.getQuarter s = none) : p.getQuarter (s.paint c) = none
L158   theorem    Gravity.getQuarter_paint_some[priv] : (s : Shape) (c : Color) (p : QuarterPos) (q : Quarter) (h : p.getQuarter s = some q) : ∃ q', p.getQuarter (s.paint c) = some q'
L171   theorem    Gravity.isStructurallyBonded_paint[priv] : (s : Shape) (c : Color) (p1 p2 : QuarterPos) : isStructurallyBonded (s.paint c) p1 p2 = isStructurallyBonded s p1 p2
L193   theorem    Gravity.isGroundingContact_paint[priv] : (s : Shape) (c : Color) (p1 p2 : QuarterPos) : isGroundingContact (s.paint c) p1 p2 = isGroundingContact s p1 p2
L220   theorem    Gravity.layerCount_paint[priv] : (s : Shape) (c : Color) : (s.paint c).layerCount = s.layerCount
L229   theorem    Gravity.allValid_paint[priv] : (s : Shape) (c : Color) : QuarterPos.allValid (s.paint c) = QuarterPos.allValid s
L234   theorem    Gravity.structuralClusterList_paint[priv] : (s : Shape) (c : Color) (pos : QuarterPos) : structuralClusterList (s.paint c) pos = structuralClusterList s pos
L241   theorem    Gravity.allStructuralClustersList_paint[priv] : (s : Shape) (c : Color) : allStructuralClustersList (s.paint c) = allStructuralClustersList s
L252   theorem    Gravity.allIsolatedPins_paint[priv] : (s : Shape) (c : Color) : allIsolatedPins (s.paint c) = allIsolatedPins s
L258   theorem    Gravity.groundedPositionsList_paint[priv] : (s : Shape) (c : Color) : groundedPositionsList (s.paint c) = groundedPositionsList s
L292   theorem    Gravity.floatingUnits_paint_eq : (s : Shape) (c : Color) : floatingUnits (s.paint c) = floatingUnits s
L304   theorem    Shape.IsSettled_paint : (s : Shape) (c : Color) (h : s.IsSettled) : (s.paint c).IsSettled
```
