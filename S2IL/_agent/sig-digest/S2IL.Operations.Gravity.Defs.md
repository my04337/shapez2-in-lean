# S2IL/Operations/Gravity/Defs.lean

- Lines: 1959
- Declarations: 120 (theorems/lemmas: 82, defs/abbrev: 37, private: 33, sorry: 0)

## Landmarks

L14    header    # Gravity (落下)
L42    namespace Gravity
L439   namespace FallingUnit

## Declarations

```
L50    def        Gravity.isStructurallyBonded : (s : Shape) (p1 p2 : QuarterPos) : Bool
L63    theorem    Gravity.isStructurallyBonded_symm : (s : Shape) (p1 p2 : QuarterPos) : isStructurallyBonded s p1 p2 = isStructurallyBonded s p2 p1
L87    def        Gravity.structuralBfs : (s : Shape) (allPos : List QuarterPos) (visited queue : List QuarterPos) : (fuel : Nat) → List QuarterPos | 0 => visited | fuel + 1 => match queue with | [] => visited | pos :: re...
L103   def        Gravity.structuralClusterList : (s : Shape) (pos : QuarterPos) : List QuarterPos
L109   def        Gravity.allStructuralClustersList : (s : Shape) : List (List QuarterPos)
L125   def        Gravity.structuralCluster : (s : Shape) (pos : QuarterPos) : Finset QuarterPos
L129   def        Gravity.allStructuralClusters : (s : Shape) : List (Finset QuarterPos)
L137   def        Gravity.allIsolatedPins : (s : Shape) : List QuarterPos
L149   def        Gravity.isGroundingContact : (s : Shape) (p1 p2 : QuarterPos) : Bool
L163   theorem    Gravity.isGroundingContact_nonEmpty : (s : Shape) (p1 p2 : QuarterPos) (h : isGroundingContact s p1 p2 = true) : ∃ q1 q2, p1.getQuarter s = some q1 ∧ p2.getQuarter s = some q2 ∧ q1.isEmpty = false ∧ ...
L179   theorem    Gravity.isStructurallyBonded_implies_isGroundingContact : (s : Shape) (p1 p2 : QuarterPos) (h : isStructurallyBonded s p1 p2 = true) : isGroundingContact s p1 p2 = true
L203   theorem    Gravity.isGroundingContact_of_layers_prefix : (s s' : Shape) (h_pfx : ∃ t, s.layers = s'.layers ++ t) (p1 p2 : QuarterPos) (h_v1 : p1.layer < s'.layerCount) (h_v2 : p2.layer < s'.layerCount) : isGrou...
L217   def        Gravity.isUpwardGroundingContact : (s : Shape) (from_ to_ : QuarterPos) : Bool
L221   theorem    Gravity.isUpwardGroundingContact_base : {s : Shape} {a b : QuarterPos} (h : isUpwardGroundingContact s a b = true) : isGroundingContact s a b = true
L228   theorem    Gravity.isGroundingContact_to_isUpwardGroundingContact : {s : Shape} {a b : QuarterPos} (h_gc : isGroundingContact s a b = true) (h_le : a.layer ≤ b.layer) : isUpwardGroundingContact s a b = true
L234   theorem    Gravity.isUpwardGroundingContact_layer_le : {s : Shape} {a b : QuarterPos} (h : isUpwardGroundingContact s a b = true) : a.layer ≤ b.layer
L242   def        Gravity.groundingEdge : (s : Shape) (a b : QuarterPos) : Bool
L246   theorem    Gravity.groundingEdge_of_isUpwardGroundingContact : {s : Shape} {a b : QuarterPos} (h : isUpwardGroundingContact s a b = true) : groundingEdge s a b = true
L252   theorem    Gravity.groundingEdge_of_isStructurallyBonded : {s : Shape} {a b : QuarterPos} (h : isStructurallyBonded s a b = true) : groundingEdge s a b = true
L258   theorem    Gravity.groundingEdge_base : {s : Shape} {a b : QuarterPos} (h : groundingEdge s a b = true) : isGroundingContact s a b = true
L270   theorem    Gravity.groundingEdge_false_of_empty_quarter : {s : Shape} {a : QuarterPos} (b : QuarterPos) (h : ∀ q, a.getQuarter s = some q → q.isEmpty = true) : groundingEdge s a b = false
L285   theorem    Gravity.groundingEdge_false_of_empty_quarter_right : {s : Shape} {b : QuarterPos} (a : QuarterPos) (h : ∀ q, b.getQuarter s = some q → q.isEmpty = true) : groundingEdge s a b = false
L301   def        Gravity.groundingBfs : (s : Shape) (allPos : List QuarterPos) (visited queue : List QuarterPos) : (fuel : Nat) → List QuarterPos | 0 => visited | fuel + 1 => match queue with | [] => visited | pos :: res...
L317   def        Gravity.groundedPositionsList : (s : Shape) : List QuarterPos
L331   def        Gravity.groundedPositions : (s : Shape) : Finset QuarterPos
L335   def        Gravity.isGrounded : (s : Shape) (pos : QuarterPos) : Bool
L344   def        Gravity.nonGroundedLayerSum : (s : Shape) : Nat
L354   def        Gravity.ngsWeight : (s : Shape) (p : QuarterPos) : Nat
L360   theorem    Gravity.ngs_foldl_eq_sum[priv] : (s : Shape) (grounded : Finset QuarterPos) (l : List QuarterPos) (acc : Nat) : l.foldl (fun acc p => match p.getQuarter s with | some q => if !q.isEmpty && p ∉ grou...
L384   theorem    Gravity.nonGroundedLayerSum_eq_sum : (s : Shape) : nonGroundedLayerSum s = ((QuarterPos.allValid s).map (ngsWeight s)).sum
L409   theorem    Gravity.ngsWeight_clearPositions_mem[priv] : (s : Shape) (ps : List QuarterPos) (p : QuarterPos) (hp : (ps.any (· == p)) = true) (hp_lt : p.layer < s.layerCount) : ngsWeight (s.clearPositions ps) p...
L418   theorem    Gravity.ngsWeight_clearPositions_not_mem[priv] : (s : Shape) (ps : List QuarterPos) (h_gp_eq : groundedPositions (s.clearPositions ps) = groundedPositions s) (p : QuarterPos) (hp : (ps.any (· == p)...
L432   inductive  Gravity.FallingUnit : where
L442   def        Gravity.FallingUnit.positions : : FallingUnit → List QuarterPos | cluster ps => ps | pin p => [p] / def minLayer (u : FallingUnit) : Nat
L447   def        Gravity.FallingUnit.minLayer : (u : FallingUnit) : Nat
L453   def        Gravity.FallingUnit.minLayerAtDir : (u : FallingUnit) (dir : Direction) : Option Nat
L461   def        Gravity.floatingUnits : (s : Shape) : List FallingUnit
L479   def        Gravity.shouldProcessBefore : (a b : FallingUnit) : Bool
L490   def        Gravity.insertSorted : (u : FallingUnit) (sorted : List FallingUnit) : (fuel : Nat) → List FallingUnit | 0 => u :: sorted | fuel + 1 => match sorted with | [] => [u] | v :: rest => if shouldProcessBefore...
L504   def        Gravity.sortFallingUnits : (units : List FallingUnit) : List FallingUnit
L515   def        Gravity.fallingUnitLe : (a b : FallingUnit) : Bool
L519   theorem    Gravity.fallingUnitLe_total : (a b : FallingUnit) : fallingUnitLe a b = true ∨ fallingUnitLe b a = true
L524   theorem    Gravity.fallingUnitLe_trans : {a b c : FallingUnit} (h1 : fallingUnitLe a b = true) (h2 : fallingUnitLe b c = true) : fallingUnitLe a c = true
L534   def        Gravity.encodeQuarterPos : (p : QuarterPos) : Nat
L542   def        FallingUnit.canonicalKey : (u : FallingUnit) : List Nat
L546   def        Gravity.listNatLe : (l1 l2 : List Nat) : Bool
L549   theorem    Gravity.listNatLe_refl : (l : List Nat) : listNatLe l l = true
L553   theorem    Gravity.listNatLe_total : (l1 l2 : List Nat) : listNatLe l1 l2 = true ∨ listNatLe l2 l1 = true
L558   theorem    Gravity.listNatLe_trans : {l1 l2 l3 : List Nat} (h1 : listNatLe l1 l2 = true) (h2 : listNatLe l2 l3 = true) : listNatLe l1 l3 = true
L564   theorem    Gravity.listNatLe_antisymm : {l1 l2 : List Nat} (h1 : listNatLe l1 l2 = true) (h2 : listNatLe l2 l1 = true) : l1 = l2
L573   def        FallingUnit.typeOrd : : FallingUnit → Nat | .pin _ => 0 | .cluster _ => 1 / theorem FallingUnit.typeOrd_le_one (u : FallingUnit) : u.typeOrd ≤ 1
L578   theorem    FallingUnit.typeOrd_le_one : (u : FallingUnit) : u.typeOrd ≤ 1
L584   def        FallingUnit.sortGroup : (u : FallingUnit) : Nat
L588   theorem    FallingUnit.sortGroup_eq_iff : {u v : FallingUnit} : u.sortGroup = v.sortGroup ↔ u.minLayer = v.minLayer ∧ u.typeOrd = v.typeOrd
L603   def        Gravity.fallingUnitOrd : (a b : FallingUnit) : Bool
L611   theorem    Gravity.fallingUnitOrd_total : (a b : FallingUnit) : fallingUnitOrd a b = true ∨ fallingUnitOrd b a = true
L630   theorem    Gravity.fallingUnitOrd_total' : (a b : FallingUnit) : (fallingUnitOrd a b || fallingUnitOrd b a) = true
L634   theorem    Gravity.fallingUnitOrd_trans : {a b c : FallingUnit} (h1 : fallingUnitOrd a b = true) (h2 : fallingUnitOrd b c = true) : fallingUnitOrd a c = true
L704   theorem    Gravity.toFinset_eq_of_any_eq : {l1 l2 : List Nat} (h : ∀ n, l1.any (· == n) = l2.any (· == n)) : l1.toFinset = l2.toFinset
L717   theorem    Gravity.canonicalKey_eq_of_any_eq : {u1 u2 : FallingUnit} (h : ∀ p : QuarterPos, u1.positions.any (· == p) = u2.positions.any (· == p)) : u1.canonicalKey = u2.canonicalKey
L740   theorem    Gravity.fallingUnitOrd_eq_of_any_eq : {a1 a2 b1 b2 : FallingUnit} (ha : ∀ p, a1.positions.any (· == p) = a2.positions.any (· == p)) (hb : ∀ p, b1.positions.any (· == p) = b2.positions.any (· == p)) (...
L750   theorem    Gravity.encodeQuarterPos_injective : : Function.Injective encodeQuarterPos
L760   theorem    Gravity.mergeSort_perm_eq : {le : α → α → Bool} (h_trans : ∀ a b c, le a b = true → le b c = true → le a c = true) (h_total : ∀ a b, (le a b || le b a) = true) {l1 l2 : List α} (h_perm : l1.Perm l2) ...
L781   def        Gravity.sortFallingUnits' : (units : List FallingUnit) : List FallingUnit
L790   def        Gravity.isOccupied : (obstacle : List Layer) (layer : Nat) (dir : Direction) : Bool
L804   theorem    Gravity.isOccupied_iff_getDir_ne_empty : (obs : List Layer) (lay : Nat) (dir : Direction) : isOccupied obs lay dir = true ↔ QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty
L830   lemma      Gravity.isOccupied_of_getDir_ne_empty : (obs : List Layer) (lay : Nat) (dir : Direction) (h : QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty) : isOccupied obs lay dir = true
L836   lemma      Gravity.getDir_ne_empty_of_isOccupied : (obs : List Layer) (lay : Nat) (dir : Direction) (h : isOccupied obs lay dir = true) : QuarterPos.getDir (obs.getD lay Layer.empty) dir ≠ Quarter.empty
L845   def        Gravity.landingDistance : (u : FallingUnit) (obstacle : List Layer) : Nat
L871   def        Gravity.placeQuarter : (layers : List Layer) (layer : Nat) (dir : Direction) (q : Quarter) : List Layer
L881   def        Gravity.placeFallingUnit : (origShape : Shape) (obstacle : List Layer) (u : FallingUnit) (dropDist : Nat) : List Layer
L898   def        Gravity.placeLDGroups : (origShape : Shape) (sorted : List FallingUnit) (obs : List Layer) : List Layer
L929   def        Gravity.waveStep : (s : Shape) : Shape
L955   theorem    Gravity.placeQuarter_ne_nil[priv] : (layers : List Layer) (layer : Nat) (d : Direction) (q : Quarter) (h : layers ≠ []) : placeQuarter layers layer d q ≠ []
L975   theorem    Gravity.placeFallingUnit_ne_nil[priv] : (s : Shape) (obs : List Layer) (u : FallingUnit) (d : Nat) (h : obs ≠ []) : placeFallingUnit s obs u d ≠ []
L989   theorem    Gravity.foldl_placeFU_fixed_ne_nil[priv] : (s : Shape) (group : List FallingUnit) (obs : List Layer) (d : Nat) (h : obs ≠ []) : group.foldl (fun acc fu => placeFallingUnit s acc fu d) obs ≠ []
L1000  theorem    Gravity.placeLDGroups_ne_nil[priv] : (s : Shape) (sorted : List FallingUnit) (obs : List Layer) (h : obs ≠ []) : placeLDGroups s sorted obs ≠ []
L1036  theorem    Gravity.clearPositions_layers_ne_nil[priv] : (s : Shape) (positions : List QuarterPos) : (s.clearPositions positions).layers ≠ []
L1046  theorem    Gravity.placeLDGroups_ofLayers_isSome[priv] : (s : Shape) (sorted : List FallingUnit) (obs : List Layer) (h : obs ≠ []) : (Shape.ofLayers (placeLDGroups s sorted obs)).isSome = true
L1058  theorem    Gravity.waveStep_layers_eq : (s : Shape) (h : (floatingUnits s).isEmpty = false) : let fus
L1101  theorem    Gravity.foldl_min_mem_or_eq_init[priv] : (init : Nat) (l : List FallingUnit) : (∃ u ∈ l, u.minLayer = l.foldl (fun acc u => min acc u.minLayer) init) ∨ l.foldl (fun acc u => min acc u.minLayer) ini...
L1117  theorem    Gravity.settling_nonempty : (fus : List FallingUnit) (h : fus.isEmpty = false) : let minML
L1146  theorem    Gravity.filter_length_partition[priv] : (l : List FallingUnit) (p : FallingUnit → Bool) : (l.filter p).length + (l.filter (fun x => !p x)).length = l.length
L1155  theorem    Gravity.groundingEdge_clearPositions_of_not_mem[priv] : (s : Shape) (ps : List QuarterPos) (a b : QuarterPos) (ha : (ps.any (· == a)) = false) (hb : (ps.any (· == b)) = false) (ha_lt : a.layer < s....
L1170  theorem    Gravity.floatingUnit_positions_not_grounded[priv] : (s : Shape) (u : FallingUnit) (hu : u ∈ floatingUnits s) (p : QuarterPos) (hp : p ∈ u.positions) : p ∉ groundedPositions s
L1192  theorem    Gravity.groundingBfs_eq_generic'[priv] : (s : Shape) (allPos vis queue : List QuarterPos) (fuel : Nat) : groundingBfs s allPos vis queue fuel = genericBfs (groundingEdge s) allPos vis queue fuel
L1206  theorem    Gravity.structuralBfs_eq_generic'[priv] : (s : Shape) (allPos vis queue : List QuarterPos) (fuel : Nat) : structuralBfs s allPos vis queue fuel = genericBfs (isStructurallyBonded s) allPos vis queu...
L1220  theorem    Gravity.isGroundingContact_valid'[priv] : (s : Shape) (p q : QuarterPos) (h : isGroundingContact s p q = true) : q.layer < s.layerCount
L1233  theorem    Gravity.isGroundingContact_valid_fst'[priv] : (s : Shape) (p q : QuarterPos) (h : isGroundingContact s p q = true) : p.layer < s.layerCount
L1246  theorem    Gravity.allValid_mem_layer_lt' : {s : Shape} {p : QuarterPos} (h : p ∈ QuarterPos.allValid s) : p.layer < s.layerCount
L1255  theorem    Gravity.allValid_any_iff_layer[priv] : (s : Shape) (p : QuarterPos) : (QuarterPos.allValid s).any (· == p) = true ↔ p.layer < s.layerCount
L1271  theorem    Gravity.allValid_length[priv] : (s : Shape) : (QuarterPos.allValid s).length = s.layerCount * 4
L1284  theorem    Gravity.groundedPositionsList_sound'[priv] : (s : Shape) (p : QuarterPos) (h : (groundedPositionsList s).any (· == p) = true) : ∃ seed, seed ∈ (QuarterPos.allValid s).filter (fun q => q.layer == 0 ...
L1302  theorem    Gravity.groundedPositionsList_fuel_adequate'[priv] : (s : Shape) : (s.layerCount * 4 * (s.layerCount * 4) + s.layerCount * 4) + 1 ≥ ((QuarterPos.allValid s).filter fun p => p.layer == 0 && match p....
L1322  theorem    Gravity.groundedPositionsList_complete'[priv] : (s : Shape) (seed p : QuarterPos) (h_seed : seed ∈ (QuarterPos.allValid s).filter (fun q => q.layer == 0 && match q.getQuarter s with | some q => !q....
L1365  theorem    Gravity.mem_groundedPositionsList_of_mem_groundedPositions[priv] : {s : Shape} {q : QuarterPos} (h : q ∈ groundedPositions s) : (groundedPositionsList s).any (· == q) = true
L1372  theorem    Gravity.mem_groundedPositions_of_any[priv] : {s : Shape} {q : QuarterPos} (h : (groundedPositionsList s).any (· == q) = true) : q ∈ groundedPositions s
L1382  theorem    Gravity.layer_zero_nonempty_grounded : (s : Shape) (p : QuarterPos) (h_av : p ∈ QuarterPos.allValid s) (h_layer : p.layer = 0) (q : Quarter) (hq : p.getQuarter s = some q) (hne : q.isEmpty = false) :...
L1404  theorem    Gravity.grounded_of_edge : {s : Shape} {a b : QuarterPos} (h_a : a ∈ groundedPositions s) (h_edge : groundingEdge s a b = true) : b ∈ groundedPositions s
L1419  theorem    Gravity.ungrounded_pin_layer_one_below_empty : (s : Shape) (q : QuarterPos) (h_av : q ∈ QuarterPos.allValid s) (h_pin : q.getQuarter s = some .pin) (h_layer : q.layer = 1) (h_ung : q ∉ groundedPositi...
L1473  theorem    Gravity.not_any_ps_of_grounded[priv] : {s : Shape} {ps : List QuarterPos} {p : QuarterPos} (h_floating : ∀ x ∈ ps, x ∉ groundedPositions s) (hp : (groundedPositionsList s).any (· == p) = true) : (p...
L1485  theorem    Gravity.allValid_eq_of_layerCount : {s₁ s₂ : Shape} (h : s₁.layerCount = s₂.layerCount) : QuarterPos.allValid s₁ = QuarterPos.allValid s₂
L1491  theorem    Gravity.allValid_mem_layer_lt : {s : Shape} {p : QuarterPos} (h : p ∈ QuarterPos.allValid s) : p.layer < s.layerCount
L1508  theorem    Gravity.clearPositions_preserves_grounded[priv] : (s : Shape) (ps : List QuarterPos) (h_floating : ∀ p ∈ ps, p ∉ groundedPositions s) (q : QuarterPos) (hq : q ∈ groundedPositions s) : q ∈ groundedP...
L1564  theorem    Gravity.grounding_propagates_structural[priv] : (s : Shape) (p q : QuarterPos) (h_bond_path : GenericReachable (fun a b => isStructurallyBonded s a b) p q) (h_grounded : q ∈ groundedPositions s) : ...
L1586  theorem    Gravity.clearPositions_grounded_reverse[priv] : (s : Shape) (ps : List QuarterPos) (_h_floating : ∀ p ∈ ps, p ∉ groundedPositions s) (q : QuarterPos) (hq : q ∈ groundedPositions (s.clearPositions p...
L1663  theorem    Gravity.groundedPositions_clearNonGrounded_eq[priv] : (s : Shape) (ps : List QuarterPos) (h_floating : ∀ p ∈ ps, p ∉ groundedPositions s) : groundedPositions (s.clearPositions ps) = groundedPositio...
L1673  theorem    Gravity.sum_map_ite_eq_sum_filter : {α : Type*} (l : List α) (P : α → Bool) (f : α → Nat) : (l.map (fun x => if P x then f x else 0)).sum = ((l.filter P).map f).sum
L1682  theorem    Gravity.sum_map_add : {α : Type*} (l : List α) (f g : α → Nat) : (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum
L1694  theorem    Gravity.nonGroundedLayerSum_clear_add : (s : Shape) (ps : List QuarterPos) (h_floating : ∀ p ∈ ps, p ∉ groundedPositions s) (_h_valid : ∀ p ∈ ps, p.layer < s.layerCount) : nonGroundedLayerSum s = non...
L1734  theorem    Gravity.landingDistance_check_ge_min[priv] : (obstacle : List Layer) (positions : List QuarterPos) (maxDrop d fuel : Nat) : landingDistance.check obstacle positions maxDrop d fuel ≥ min d maxDrop
L1755  theorem    Gravity.landingDistance_ge_one[priv] : (u : FallingUnit) (obstacle : List Layer) (h_ml : u.minLayer ≥ 1) : landingDistance u obstacle ≥ 1
L1769  theorem    Gravity.allValid_nodup : (s : Shape) : (QuarterPos.allValid s).Nodup
L1787  theorem    Gravity.allStructuralClustersList_nodup : (s : Shape) : (allStructuralClustersList s).Nodup
L1835  theorem    Gravity.floatingUnits_nodup : (s : Shape) : (floatingUnits s).Nodup
L1855  theorem    Gravity.floatingUnits_positions_nongrounded : (s : Shape) {u : FallingUnit} (hu : u ∈ floatingUnits s) {p : QuarterPos} (hp : p ∈ u.positions) : p ∉ groundedPositions s
L1882  theorem    Gravity.settling_positions_nongrounded : (s : Shape) {P : FallingUnit → Bool} {u : FallingUnit} (hu : u ∈ (floatingUnits s).filter P) {p : QuarterPos} (hp : p ∈ u.positions) : p ∉ groundedPositions s
L1894  theorem    Gravity.structuralClusterList_contains_seed[priv] : (s : Shape) (pos : QuarterPos) (h_lc : s.layerCount > 0) : (structuralClusterList s pos).any (· == pos) = true
L1902  theorem    Gravity.allStructuralClustersList_ne_nil[priv] : (s : Shape) : ∀ c ∈ allStructuralClustersList s, c ≠ []
L1936  theorem    Gravity.floatingUnits_positions_ne_nil : (s : Shape) (u : FallingUnit) (hu : u ∈ floatingUnits s) : u.positions ≠ []
```
