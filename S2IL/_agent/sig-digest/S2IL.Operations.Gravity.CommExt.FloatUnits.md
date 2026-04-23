# S2IL/Operations/Gravity/CommExt/FloatUnits.lean

- Lines: 952
- Declarations: 41 (theorems/lemmas: 41, defs/abbrev: 0, private: 1, sorry: 0)

## Landmarks

L7     namespace Gravity

## Declarations

```
L16    theorem    Gravity.ungrounded_in_floatingUnits_positions : (s : Shape) (p : QuarterPos) (h_valid : p.layer < s.layerCount) (h_ne : ∃ q, p.getQuarter s = some q ∧ !q.isEmpty = true) (h_ug : p ∉ groundedPositions...
L92    theorem    Gravity.floatingUnits_positions_getQuarter : (s : Shape) (p : QuarterPos) (h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true) : p.layer < s.layerCount ∧ (∃ q, p.getQuarter s =...
L153   theorem    Gravity.falling_positions_any_rotate180 : (s : Shape) (p : QuarterPos) : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = ((floatingUnits s.rotate180).flatMap FallingUnit.positions).a...
L184   theorem    Gravity.ngsWeight_eq_layer_succ_of_mem_floatingUnits_positions : (s : Shape) (p : QuarterPos) (h : ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true) : ngsWeight s p = p.layer + 1
L195   theorem    Gravity.map_ngsWeight_eq_map_layer_succ_of_subset_floatingUnits_positions : (s : Shape) (ps : List QuarterPos) (h : ∀ p ∈ ps, ((floatingUnits s).flatMap FallingUnit.positions).any (· == p) = true) : ...
L204   theorem    Gravity.beq_rotate180_comm : (x p : QuarterPos) : (x.rotate180 == p) = (x == p.rotate180)
L211   theorem    Gravity.any_map_rotate180_beq : (ps : List QuarterPos) (p : QuarterPos) : (ps.map QuarterPos.rotate180).any (· == p) = ps.any (· == p.rotate180)
L224   theorem    Gravity.any_pred_ext : {l1 l2 : List QuarterPos} (h : ∀ p, l1.any (· == p) = l2.any (· == p)) (f : QuarterPos → Bool) : l1.any f = l2.any f
L250   theorem    Gravity.foldl_min_le_init : (l : List QuarterPos) (init : Nat) : l.foldl (fun acc q => min acc q.layer) init ≤ init
L259   theorem    Gravity.foldl_min_le_elem : (l : List QuarterPos) (init : Nat) (q : QuarterPos) (hq : q ∈ l) : l.foldl (fun acc p => min acc p.layer) init ≤ q.layer
L274   theorem    Gravity.foldl_min_le_mem : (p : QuarterPos) (rest : List QuarterPos) (x : QuarterPos) (hx : x ∈ p :: rest) : rest.foldl (fun acc q => min acc q.layer) p.layer ≤ x.layer
L282   theorem    Gravity.foldl_min_attained : (l : List QuarterPos) (init : Nat) : l.foldl (fun acc q => min acc q.layer) init = init ∨ ∃ q ∈ l, l.foldl (fun acc q => min acc q.layer) init = q.layer
L299   theorem    Gravity.mem_of_any_beq_eq : {l1 l2 : List QuarterPos} (h : ∀ p, l1.any (· == p) = l2.any (· == p)) {x : QuarterPos} (hx : x ∈ l2) : x ∈ l1
L309   theorem    Gravity.minLayer_ext : {u1 u2 : FallingUnit} (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p)) : u1.minLayer = u2.minLayer
L362   theorem    Gravity.landingDistance_ext : {u1 u2 : FallingUnit} (h : ∀ p, u1.positions.any (· == p) = u2.positions.any (· == p)) (obs : List Layer) : landingDistance u1 obs = landingDistance u2 obs
L383   theorem    Gravity.setDir_setDir_comm : (l : Layer) {d1 d2 : Direction} (q1 q2 : Quarter) (h : d1 ≠ d2) : QuarterPos.setDir (QuarterPos.setDir l d1 q1) d2 q2 = QuarterPos.setDir (QuarterPos.setDir l d2 q2) d1 q1
L390   theorem    Gravity.setDir_setDir_same : (l : Layer) (d : Direction) (q1 q2 : Quarter) : QuarterPos.setDir (QuarterPos.setDir l d q1) d q2 = QuarterPos.setDir l d q2
L396   theorem    Gravity.placeQuarter_getElem?_full : (obs : List Layer) (lay i : Nat) (d : Direction) (q : Quarter) : (placeQuarter obs lay d q)[i]? = if i < max obs.length (lay + 1) then if i = lay then some (Quart...
L466   theorem    Gravity.placeQuarter_length : (obs : List Layer) (lay : Nat) (d : Direction) (q : Quarter) : (placeQuarter obs lay d q).length = max obs.length (lay + 1)
L483   theorem    Gravity.placeQuarter_getD : (obs : List Layer) (lay i : Nat) (d : Direction) (q : Quarter) (hi : i < max obs.length (lay + 1)) : (placeQuarter obs lay d q).getD i Layer.empty = if i = lay then Quarte...
L493   theorem    Gravity.placeQuarter_getD_ne : (obs : List Layer) (lay i : Nat) (d : Direction) (q : Quarter) (hne : i ≠ lay) : (placeQuarter obs lay d q).getD i Layer.empty = obs.getD i Layer.empty
L504   theorem    Gravity.placeQuarter_idem : (obs : List Layer) (lay : Nat) (d : Direction) (q : Quarter) : placeQuarter (placeQuarter obs lay d q) lay d q = placeQuarter obs lay d q
L525   theorem    Gravity.placeQuarter_comm_layer_ne : (obs : List Layer) (l1 l2 : Nat) (d1 d2 : Direction) (q1 q2 : Quarter) (hne : l1 ≠ l2) : placeQuarter (placeQuarter obs l1 d1 q1) l2 d2 q2 = placeQuarter (placeQu...
L559   theorem    Gravity.placeQuarter_comm_dir_ne : (obs : List Layer) (lay : Nat) (d1 d2 : Direction) (q1 q2 : Quarter) (hne : d1 ≠ d2) : placeQuarter (placeQuarter obs lay d1 q1) lay d2 q2 = placeQuarter (placeQuar...
L583   theorem    Gravity.foldl_absorb : {β : Type} (f : β → QuarterPos → β) (S : QuarterPos → Prop) (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1) (h_idem : ∀ p, S p → ∀ s, f (f s p) p...
L607   theorem    Gravity.foldl_extract : {β : Type} (f : β → QuarterPos → β) (S : QuarterPos → Prop) (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1) (h_idem : ∀ p, S p → ∀ s, f (f s p) ...
L648   theorem    Gravity.foldl_any_eq_of_comm_idem : {β : Type} (f : β → QuarterPos → β) (S : QuarterPos → Prop) (h_comm : ∀ p1 p2, S p1 → S p2 → p1 ≠ p2 → ∀ s, f (f s p1) p2 = f (f s p2) p1) (h_idem : ∀ p, S p → ∀ s...
L739   theorem    Gravity.minLayer_le_layer : {u : FallingUnit} {p : QuarterPos} (hp : p ∈ u.positions) (d : Nat) (hd : d ≤ u.minLayer) : d ≤ p.layer
L763   theorem    Gravity.landing_shift_injective_of_layer_ge : {d : Nat} {p q : QuarterPos} (hp : d ≤ p.layer) (hq : d ≤ q.layer) (h_l : p.layer - d = q.layer - d) (h_dir : p.dir = q.dir) : p = q
L773   theorem    Gravity.landing_map_nodup_of_layer_ge : (l : List QuarterPos) (d : Nat) (h_ge : ∀ p ∈ l, d ≤ p.layer) (h_nd : l.Nodup) : (l.map (fun p => (p.layer - d, p.dir))).Nodup
L784   theorem    Gravity.landing_shift_injective_on_fu : {u : FallingUnit} {d : Nat} (hd : d ≤ u.minLayer) {p q : QuarterPos} (hp : p ∈ u.positions) (hq : q ∈ u.positions) (h_l : p.layer - d = q.layer - d) (h_dir : p...
L794   theorem    Gravity.landing_map_nodup_on_fu : (u : FallingUnit) (d : Nat) (hd : d ≤ u.minLayer) (h_nd : u.positions.Nodup) : (u.positions.map (fun p => (p.layer - d, p.dir))).Nodup
L802   theorem    Gravity.pin_positions_nodup : (p : QuarterPos) : (FallingUnit.pin p).positions.Nodup
L808   theorem    Gravity.structuralClusterList_nodup : (s : Shape) (pos : QuarterPos) : (structuralClusterList s pos).Nodup
L820   theorem    Gravity.allStructuralClustersList_pairwise_disjoint : (s : Shape) : (allStructuralClustersList s).Pairwise List.Disjoint
L835   theorem    Gravity.cluster_position_bondable : (s : Shape) {c : List QuarterPos} (hc : c ∈ allStructuralClustersList s) {p : QuarterPos} (hp : p ∈ c) : ∃ w, p.getQuarter s = some w ∧ w.canFormBond = true
L846   theorem    Gravity.pin_position_getQuarter[priv] : (s : Shape) {p : QuarterPos} (hp : p ∈ allIsolatedPins s) : p.getQuarter s = some Quarter.pin
L865   theorem    Gravity.floatingUnits_positions_pairwise_disjoint : (s : Shape) : (floatingUnits s).Pairwise (fun u v => List.Disjoint u.positions v.positions)
L910   theorem    Gravity.floatingUnits_flatMap_positions_nodup : (s : Shape) : ((floatingUnits s).flatMap FallingUnit.positions).Nodup
L931   theorem    Gravity.foldl_min_fu_le_init : (l : List FallingUnit) (init : Nat) : l.foldl (fun acc u => min acc u.minLayer) init ≤ init
L940   theorem    Gravity.foldl_min_fu_le_mem : (l : List FallingUnit) (init : Nat) {u : FallingUnit} (hu : u ∈ l) : l.foldl (fun acc v => min acc v.minLayer) init ≤ u.minLayer
```
