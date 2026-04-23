# S2IL/Operations/Gravity/Facade.lean

- Lines: 949
- Declarations: 51 (theorems/lemmas: 43, defs/abbrev: 7, private: 38, sorry: 0)

## Landmarks

L6     namespace Gravity
L875   namespace Shape
L935   namespace SettledShape

## Declarations

```
L15    theorem    Gravity.process_rotate180 : (s : Shape) : (process s).map Shape.rotate180 = process s.rotate180
L31    def        FallingUnit.rotateCW[priv] : : FallingUnit → FallingUnit | .cluster ps => .cluster (ps.map QuarterPos.rotateCW) | .pin p => .pin p.rotateCW / private theorem FallingUnit.positions_rotateCW (u :...
L36    theorem    FallingUnit.positions_rotateCW[priv] : (u : FallingUnit) : u.rotateCW.positions = u.positions.map QuarterPos.rotateCW
L43    theorem    QuarterPos.rotateCW_layer[priv] : (p : QuarterPos) : p.rotateCW.layer = p.layer
L47    theorem    QuarterPos.rotateCW_dir[priv] : (p : QuarterPos) : p.rotateCW.dir = p.dir.rotateCW
L51    theorem    Gravity.foldl_map_layer_cw[priv] : (l : List QuarterPos) (init : Nat) : (l.map QuarterPos.rotateCW).foldl (fun a q => min a q.layer) init = l.foldl (fun a q => min a q.layer) init
L57    theorem    FallingUnit.minLayer_rotateCW[priv] : (u : FallingUnit) : u.rotateCW.minLayer = u.minLayer
L65    theorem    FallingUnit.typeOrd_rotateCW[priv] : (u : FallingUnit) : u.rotateCW.typeOrd = u.typeOrd
L70    theorem    FallingUnit.sortGroup_rotateCW[priv] : (u : FallingUnit) : u.rotateCW.sortGroup = u.sortGroup
L82    theorem    Gravity.ofLayers_rotateCW[priv] : (ls : List Layer) : (Shape.ofLayers ls).map Shape.rotateCW = Shape.ofLayers (ls.map Layer.rotateCW)
L92    theorem    Gravity.option_bind_normalize_rotateCW[priv] : (os : Option Shape) : (os.bind Shape.normalize).map Shape.rotateCW = (os.map Shape.rotateCW).bind Shape.normalize
L102   theorem    Gravity.isOccupied_rotateCW[priv] : (obs : List Layer) (layer : Nat) (d : Direction) : isOccupied (obs.map Layer.rotateCW) layer (d.rotateCW) = isOccupied obs layer d
L111   theorem    Gravity.landed_rotateCW[priv] : (positions : List QuarterPos) (obs : List Layer) (d : Nat) : (positions.map QuarterPos.rotateCW).any (fun p => let newLayer
L129   theorem    Gravity.landingDistance_check_rotateCW[priv] : (positions : List QuarterPos) (obs : List Layer) (maxDrop d fuel : Nat) : landingDistance.check (obs.map Layer.rotateCW) (positions.map QuarterPos.rot...
L145   theorem    Gravity.landingDistance_rotateCW[priv] : (u : FallingUnit) (obs : List Layer) : landingDistance u.rotateCW (obs.map Layer.rotateCW) = landingDistance u obs
L152   theorem    Gravity.setDir_rotateCW[priv] : (l : Layer) (d : Direction) (q : Quarter) : (QuarterPos.setDir l d q).rotateCW = QuarterPos.setDir (l.rotateCW) (d.rotateCW) q
L158   theorem    Gravity.replicate_empty_rotateCW[priv] : (n : Nat) : (List.replicate n Layer.empty).map Layer.rotateCW = List.replicate n Layer.empty
L169   theorem    Gravity.placeQuarter_rotateCW[priv] : (layers : List Layer) (lay : Nat) (d : Direction) (q : Quarter) : (placeQuarter layers lay d q).map Layer.rotateCW = placeQuarter (layers.map Layer.rotateCW) l...
L191   theorem    Gravity.placeFallingUnit_rotateCW[priv] : (origShape : Shape) (obs : List Layer) (u : FallingUnit) (dropDist : Nat) : (placeFallingUnit origShape obs u dropDist).map Layer.rotateCW = placeFallingUn...
L226   theorem    Gravity.flatMap_map_rotateCW[priv] : (units : List FallingUnit) : (units.map FallingUnit.rotateCW).flatMap FallingUnit.positions = (units.flatMap FallingUnit.positions).map QuarterPos.rotateCW
L232   theorem    Gravity.foldl_place_rotateCW[priv] : (s : Shape) (sorted : List FallingUnit) (obs : List Layer) : (sorted.foldl (fun obs u => let d
L253   theorem    Gravity.takeWhile_map_comm[priv] : {f : α → β} {p : β → Bool} {q : α → Bool} (h : ∀ x, p (f x) = q x) (l : List α) : (l.map f).takeWhile p = (l.takeWhile q).map f
L262   theorem    Gravity.dropWhile_map_comm[priv] : {f : α → β} {p : β → Bool} {q : α → Bool} (h : ∀ x, p (f x) = q x) (l : List α) : (l.map f).dropWhile p = (l.dropWhile q).map f
L271   theorem    Gravity.foldl_place_fixed_d_rotateCW[priv] : (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat) : (group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs).map Layer.rotateCW =...
L284   theorem    Gravity.placeLDGroups_rotateCW[priv] : (s : Shape) (sorted : List FallingUnit) (obs : List Layer) : (placeLDGroups s sorted obs).map Layer.rotateCW = placeLDGroups s.rotateCW (sorted.map FallingUni...
L330   theorem    Gravity.any_map_rotateCW_beq : (ps : List QuarterPos) (p : QuarterPos) : (ps.map QuarterPos.rotateCW).any (· == p) = ps.any (· == p.rotateCCW)
L341   theorem    Gravity.floatingUnit_any_in_rotateCW_cluster[priv] : (s : Shape) (ps : List QuarterPos) (hu : FallingUnit.cluster ps ∈ floatingUnits s) : ∃ v ∈ floatingUnits s.rotateCW, (∀ p, (FallingUnit.cluster ...
L452   theorem    Gravity.floatingUnit_any_in_rotateCW_pin[priv] : (s : Shape) (p : QuarterPos) (hu : FallingUnit.pin p ∈ floatingUnits s) : ∃ v ∈ floatingUnits s.rotateCW, (∀ q, (FallingUnit.pin p).rotateCW.positio...
L509   theorem    Gravity.floatingUnit_any_in_rotateCW[priv] : (s : Shape) (u : FallingUnit) (hu : u ∈ floatingUnits s) : ∃ v ∈ floatingUnits s.rotateCW, (∀ p, u.rotateCW.positions.any (· == p) = v.positions.any (· ...
L525   theorem    Gravity.beq_rotateCW_iff[priv] : (q p : QuarterPos) : (q.rotateCW == p) = (q == p.rotateCCW)
L536   theorem    Gravity.beq_rotate180_iff[priv] : (q p : QuarterPos) : (q.rotate180 == p) = (q == p.rotate180)
L547   theorem    QuarterPos.rotateCCW_rotate180[priv] : (p : QuarterPos) : p.rotateCCW.rotate180 = p.rotateCW
L554   theorem    Gravity.any_map_rotateCW[priv] : (l : List QuarterPos) (p : QuarterPos) : (l.map QuarterPos.rotateCW).any (· == p) = l.any (· == p.rotateCCW)
L559   theorem    Gravity.any_map_rotate180[priv] : (l : List QuarterPos) (p : QuarterPos) : (l.map QuarterPos.rotate180).any (· == p) = l.any (· == p.rotate180)
L568   theorem    Gravity.floatingUnit_any_in_rotateCW_rev[priv] : (s : Shape) (v : FallingUnit) (hv : v ∈ floatingUnits s.rotateCW) : ∃ u ∈ floatingUnits s, (∀ p, u.rotateCW.positions.any (· == p) = v.positions.any...
L608   theorem    Gravity.foldl_min_fu_eq_init_or_mem[priv] : (l : List FallingUnit) (init : Nat) : l.foldl (fun acc u => min acc u.minLayer) init = init ∨ ∃ u ∈ l, l.foldl (fun acc u => min acc u.minLayer) init = u...
L623   theorem    Gravity.minML_eq_rotateCW[priv] : (s : Shape) (h : (floatingUnits s).isEmpty = false) : let fus
L703   theorem    Gravity.settling_positions_any_rotateCW[priv] : (s : Shape) (h : (floatingUnits s).isEmpty = false) : let fus
L812   axiom      Gravity.waveStep_rotateCW_comm[priv] : (s : Shape) : waveStep s.rotateCW = (waveStep s).rotateCW / private theorem processWave_rotateCW_comm (s : Shape) : processWave s.rotateCW = (processWave s).rot...
L816   theorem    Gravity.processWave_rotateCW_comm[priv] : (s : Shape) : processWave s.rotateCW = (processWave s).rotateCW
L865   theorem    Gravity.process_rotateCW : (s : Shape) : (process s).map Shape.rotateCW = process s.rotateCW
L878   def        Shape.gravity : (s : Shape) : Option Shape
L882   def        Shape.gravityOrSelf : (s : Shape) : Shape
L887   theorem    Shape.gravity_rotate180_comm : (s : Shape) : (s.gravity).map Shape.rotate180 = s.rotate180.gravity
L893   theorem    Shape.gravity_rotateCW_comm : (s : Shape) : (s.gravity).map Shape.rotateCW = s.rotateCW.gravity
L902   def        Shape.IsSettled : (s : Shape) : Prop
L906   def        Shape.isSettled : (s : Shape) : Bool
L910   theorem    Shape.IsSettled_iff_isSettled : (s : Shape) : s.IsSettled ↔ s.isSettled = true
L915   theorem    Shape.IsSettled_rotate180 : (s : Shape) (h : s.IsSettled) : s.rotate180.IsSettled
L933   abbrev     Shape.SettledShape : 
L942   def        Shape.SettledShape.rotate180 : (ss : SettledShape) : SettledShape
```
