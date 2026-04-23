# S2IL/Kernel/Bond/CrystalBond.lean

- Lines: 656
- Declarations: 42 (theorems/lemmas: 34, defs/abbrev: 8, private: 17, sorry: 0)

## Landmarks

L11    header    # CrystalBond (結晶結合)
L37    namespace CrystalBond

## Declarations

```
L45    def        CrystalBond.isBondedInLayer : (s : Shape) (p1 p2 : QuarterPos) : Bool
L54    def        CrystalBond.isBondedCrossLayer : (s : Shape) (p1 p2 : QuarterPos) : Bool
L62    def        CrystalBond.isBonded : (s : Shape) (p1 p2 : QuarterPos) : Bool
L72    theorem    CrystalBond.crystal_agree_symm[priv] : (q1 q2 : Option Quarter) : (match q1, q2 with | some (.crystal _), some (.crystal _) => true | _, _ => false) = (match q2, q1 with | some (.crystal _), some (.cry...
L78    theorem    CrystalBond.isBondedInLayer_symm : (s : Shape) (p1 p2 : QuarterPos) : isBondedInLayer s p1 p2 = isBondedInLayer s p2 p1
L86    theorem    CrystalBond.isBondedCrossLayer_symm : (s : Shape) (p1 p2 : QuarterPos) : isBondedCrossLayer s p1 p2 = isBondedCrossLayer s p2 p1
L95    theorem    CrystalBond.isBonded_symm : (s : Shape) (p1 p2 : QuarterPos) : isBonded s p1 p2 = isBonded s p2 p1
L105   def        CrystalBond.clusterList : (s : Shape) (pos : QuarterPos) : List QuarterPos
L112   def        CrystalBond.cluster : (s : Shape) (pos : QuarterPos) : Finset QuarterPos
L116   def        CrystalBond.allClusters : (s : Shape) : List (Finset QuarterPos)
L141   theorem    CrystalBond.isBondedInLayer_rotate180 : @[aesop norm simp] theorem isBondedInLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) : isBondedInLayer (s.rotate180) (p1.rotate180) (p2.rotate180) = isBondedInLayer s p1 p2
L148   theorem    CrystalBond.isBondedCrossLayer_rotate180 : @[aesop norm simp] theorem isBondedCrossLayer_rotate180 (s : Shape) (p1 p2 : QuarterPos) : isBondedCrossLayer (s.rotate180) (p1.rotate180) (p2.rotate180) = isBondedCrossLayer s p1 p2
L157   theorem    CrystalBond.isBonded_rotate180 : @[aesop norm simp] theorem isBonded_rotate180 (s : Shape) (p1 p2 : QuarterPos) : isBonded (s.rotate180) (p1.rotate180) (p2.rotate180) = isBonded s p1 p2
L167   abbrev     CrystalBond.σ_r180[priv] : 
L170   theorem    CrystalBond.filter_isBonded_map_rotate180[priv] : (s : Shape) (pos : QuarterPos) (visited : List QuarterPos) (allPos : List QuarterPos) : (allPos.map QuarterPos.rotate180).filter (fun p => isBonded s.r...
L189   theorem    CrystalBond.genericBfs_isBonded_rotate180[priv] : (s : Shape) (allPos visited queue : List QuarterPos) (fuel : Nat) : genericBfs (isBonded s.rotate180) (allPos.map QuarterPos.rotate180) (visited.map Qu...
L219   theorem    CrystalBond.allValid_rotate180 : (s : Shape) : QuarterPos.allValid s.rotate180 = QuarterPos.allValid s
L225   theorem    CrystalBond.clusterList_rotate180_mapped[priv] : (s : Shape) (pos : QuarterPos) : genericBfs (isBonded s.rotate180) ((QuarterPos.allValid s).map QuarterPos.rotate180) [] [pos.rotate180] (s.layerCount *...
L240   theorem    CrystalBond.genReachable_isBonded_rotate180[priv] : (s : Shape) (p q : QuarterPos) (h : GenericReachable (isBonded s) p q) : GenericReachable (isBonded s.rotate180) p.rotate180 q.rotate180
L253   theorem    CrystalBond.allValid_any_iff_layer[priv] : (s : Shape) (p : QuarterPos) : (QuarterPos.allValid s).any (· == p) = true ↔ p.layer < s.layerCount
L281   theorem    CrystalBond.allValid_any_rotate180 : (s : Shape) (p : QuarterPos) : (QuarterPos.allValid s).any (· == p.rotate180) = (QuarterPos.allValid s).any (· == p)
L298   theorem    CrystalBond.allValid_map_rotate180_any[priv] : (s : Shape) (p : QuarterPos) : ((QuarterPos.allValid s).map QuarterPos.rotate180).any (· == p) = (QuarterPos.allValid s).any (· == p)
L337   theorem    CrystalBond.isBonded_valid[priv] : (s : Shape) (p q : QuarterPos) (h : isBonded s p q = true) : q.layer < s.layerCount
L362   theorem    CrystalBond.isBonded_valid_fst[priv] : (s : Shape) (p q : QuarterPos) (h : isBonded s p q = true) : p.layer < s.layerCount
L387   theorem    CrystalBond.allValid_contains_isBonded_fst[priv] : (s : Shape) (p q : QuarterPos) (h : isBonded s p q = true) : (QuarterPos.allValid s).any (· == p) = true
L397   theorem    CrystalBond.allValid_length[priv] : (s : Shape) : (QuarterPos.allValid s).length = s.layerCount * 4
L409   theorem    CrystalBond.allValid_contains_isBonded[priv] : (s : Shape) (p q : QuarterPos) (h : isBonded s p q = true) : (QuarterPos.allValid s).any (· == q) = true
L419   theorem    CrystalBond.any_beq_iff_mem[priv] : (l : List QuarterPos) (p : QuarterPos) : l.any (· == p) = true ↔ p ∈ l
L426   theorem    CrystalBond.cluster_sound : (s : Shape) (start p : QuarterPos) : p ∈ cluster s start → GenericReachable (isBonded s) start p
L449   theorem    CrystalBond.cluster_complete : (s : Shape) (start p : QuarterPos) (h_lc : s.layerCount > 0) (h_reach : GenericReachable (isBonded s) start p) : p ∈ cluster s start
L483   theorem    CrystalBond.cluster_rotate180 : (s : Shape) (start : QuarterPos) : cluster s.rotate180 start.rotate180 = (cluster s start).image QuarterPos.rotate180
L523   theorem    CrystalBond.cluster_mem_rotate180 : (s : Shape) (start p : QuarterPos) : p ∈ cluster s start ↔ p.rotate180 ∈ cluster s.rotate180 start.rotate180
L539   abbrev     CrystalBond.σ_rCW[priv] : 
L542   theorem    CrystalBond.isBondedInLayer_rotateCW : @[aesop norm simp] theorem isBondedInLayer_rotateCW (s : Shape) (p1 p2 : QuarterPos) : isBondedInLayer (s.rotateCW) (p1.rotateCW) (p2.rotateCW) = isBondedInLayer s p1 p2
L549   theorem    CrystalBond.isBondedCrossLayer_rotateCW : @[aesop norm simp] theorem isBondedCrossLayer_rotateCW (s : Shape) (p1 p2 : QuarterPos) : isBondedCrossLayer (s.rotateCW) (p1.rotateCW) (p2.rotateCW) = isBondedCrossLayer s p1 p2
L556   theorem    CrystalBond.isBonded_rotateCW : @[aesop norm simp] theorem isBonded_rotateCW (s : Shape) (p1 p2 : QuarterPos) : isBonded (s.rotateCW) (p1.rotateCW) (p2.rotateCW) = isBonded s p1 p2
L562   theorem    CrystalBond.allValid_rotateCW : (s : Shape) : QuarterPos.allValid s.rotateCW = QuarterPos.allValid s
L568   theorem    CrystalBond.genReachable_isBonded_rotateCW[priv] : (s : Shape) (p q : QuarterPos) (h : GenericReachable (isBonded s) p q) : GenericReachable (isBonded s.rotateCW) p.rotateCW q.rotateCW
L577   theorem    CrystalBond.genReachable_isBonded_rotateCW_inv[priv] : (s : Shape) (p q : QuarterPos) (h : GenericReachable (isBonded s.rotateCW) p q) : GenericReachable (isBonded s) p.rotateCCW q.rotateCCW
L588   theorem    CrystalBond.cluster_rotateCW : (s : Shape) (start : QuarterPos) : cluster s.rotateCW start.rotateCW = (cluster s start).image QuarterPos.rotateCW
L621   theorem    CrystalBond.allValid_any_rotateCW : (s : Shape) (p : QuarterPos) : (QuarterPos.allValid s).any (· == p.rotateCW) = (QuarterPos.allValid s).any (· == p)
L639   theorem    CrystalBond.allValid_any_rotateCCW : (s : Shape) (p : QuarterPos) : (QuarterPos.allValid s).any (· == p.rotateCCW) = (QuarterPos.allValid s).any (· == p)
```
