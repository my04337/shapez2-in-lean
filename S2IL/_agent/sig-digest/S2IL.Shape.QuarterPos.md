# S2IL/Shape/QuarterPos.lean

- Lines: 585
- Declarations: 56 (theorems/lemmas: 35, defs/abbrev: 19, private: 1, sorry: 0)

## Landmarks

L7     header    # QuarterPos (象限位置)
L63    namespace Direction
L178   namespace LayerIndex
L213   namespace QuarterPos
L313   namespace Shape
L325   namespace QuarterPos
L500   namespace Shape

## Declarations

```
L59    inductive  Direction : where
L66    def        Direction.adjacent : : Direction → Direction → Bool | ne, se | se, ne => true | se, sw | sw, se => true | sw, nw | nw, sw => true | nw, ne | ne, nw => true | _, _ => false / def isEast : Direction → Bool |...
L74    def        Direction.isEast : : Direction → Bool | ne | se => true | sw | nw => false / def isWest : Direction → Bool | ne | se => false | sw | nw => true / def all : List Direction
L79    def        Direction.isWest : : Direction → Bool | ne | se => false | sw | nw => true / def all : List Direction
L84    def        Direction.all : : List Direction
L87    def        Direction.rotate180 : : Direction → Direction | ne => sw | se => nw | sw => ne | nw => se / theorem adjacent_symm (d1 d2 : Direction) : d1.adjacent d2 = d2.adjacent d1
L98    theorem    Direction.adjacent_symm : (d1 d2 : Direction) : d1.adjacent d2 = d2.adjacent d1
L102   theorem    Direction.not_adjacent_self : (d : Direction) : d.adjacent d = false
L106   theorem    Direction.isWest_eq_not_isEast : (d : Direction) : d.isWest = !d.isEast
L110   theorem    Direction.rotate180_rotate180 : @[simp] theorem rotate180_rotate180 (d : Direction) : d.rotate180.rotate180 = d
L114   theorem    Direction.isEast_rotate180 : @[aesop norm simp] theorem isEast_rotate180 (d : Direction) : d.rotate180.isEast = d.isWest
L118   theorem    Direction.isWest_rotate180 : @[aesop norm simp] theorem isWest_rotate180 (d : Direction) : d.rotate180.isWest = d.isEast
L122   theorem    Direction.adjacent_rotate180 : @[aesop norm simp] theorem adjacent_rotate180 (d1 d2 : Direction) : d1.rotate180.adjacent d2.rotate180 = d1.adjacent d2
L127   def        Direction.rotateCW : : Direction → Direction | ne => se | se => sw | sw => nw | nw => ne / def rotateCCW : Direction → Direction | ne => nw | se => ne | sw => se | nw => sw / @[simp] theorem rotateCW_rotat...
L134   def        Direction.rotateCCW : : Direction → Direction | ne => nw | se => ne | sw => se | nw => sw / @[simp] theorem rotateCW_rotateCCW (d : Direction) : d.rotateCW.rotateCCW = d
L141   theorem    Direction.rotateCW_rotateCCW : @[simp] theorem rotateCW_rotateCCW (d : Direction) : d.rotateCW.rotateCCW = d
L145   theorem    Direction.rotateCCW_rotateCW : @[simp] theorem rotateCCW_rotateCW (d : Direction) : d.rotateCCW.rotateCW = d
L149   theorem    Direction.rotateCW_rotateCW : @[aesop norm simp] theorem rotateCW_rotateCW (d : Direction) : d.rotateCW.rotateCW = d.rotate180
L153   theorem    Direction.adjacent_rotateCW : @[aesop norm simp] theorem adjacent_rotateCW (d1 d2 : Direction) : d1.rotateCW.adjacent d2.rotateCW = d1.adjacent d2
L158   def        Direction.toFin : : Direction → Fin 4 | ne => 0 | se => 1 | sw => 2 | nw => 3 / theorem toFin_injective : Function.Injective toFin
L165   theorem    Direction.toFin_injective : : Function.Injective toFin
L181   def        LayerIndex.verticallyAdjacent : (i j : Nat) : Bool
L189   theorem    LayerIndex.verticallyAdjacent_symm : (i j : Nat) : verticallyAdjacent i j = verticallyAdjacent j i
L194   theorem    LayerIndex.not_verticallyAdjacent_self : (i : Nat) : verticallyAdjacent i i = false
L206   structure  QuarterPos : where
L216   def        QuarterPos.getDir : (l : Layer) : Direction → Quarter | .ne => l.ne | .se => l.se | .sw => l.sw | .nw => l.nw / theorem getDir_nonEmpty_implies_not_isEmpty (l : Layer) (d : Direction) (hne : (getDir l d).is...
L223   theorem    QuarterPos.getDir_nonEmpty_implies_not_isEmpty : (l : Layer) (d : Direction) (hne : (getDir l d).isEmpty = false) : l.isEmpty = false
L230   theorem    Layer.ext_getDir : {l₁ l₂ : Layer} (h : ∀ d : Direction, getDir l₁ d = getDir l₂ d) : l₁ = l₂
L239   def        QuarterPos.getQuarter : (s : Shape) (pos : QuarterPos) : Option Quarter
L245   def        QuarterPos.setDir : (l : Layer) (d : Direction) (q : Quarter) : Layer
L253   def        QuarterPos.setQuarter : (s : Shape) (pos : QuarterPos) (q : Quarter) : Shape
L265   def        QuarterPos.isValid : (s : Shape) (pos : QuarterPos) : Bool
L269   def        QuarterPos.allValid : (s : Shape) : List QuarterPos
L274   def        QuarterPos.rotate180 : (p : QuarterPos) : QuarterPos
L278   theorem    QuarterPos.rotate180_rotate180 : @[simp] theorem rotate180_rotate180 (p : QuarterPos) : p.rotate180.rotate180 = p
L282   def        QuarterPos.rotateCW : (p : QuarterPos) : QuarterPos
L286   def        QuarterPos.rotateCCW : (p : QuarterPos) : QuarterPos
L290   theorem    QuarterPos.rotateCW_rotateCCW : @[simp] theorem rotateCW_rotateCCW (p : QuarterPos) : p.rotateCW.rotateCCW = p
L294   theorem    QuarterPos.rotateCCW_rotateCW : @[simp] theorem rotateCCW_rotateCW (p : QuarterPos) : p.rotateCCW.rotateCW = p
L316   def        Shape.clearPositions : (s : Shape) (positions : List QuarterPos) : Shape
L328   theorem    QuarterPos.setDir_empty_empty[priv] : (d : Direction) : setDir Layer.empty d .empty = Layer.empty
L333   theorem    QuarterPos.setDir_empty_comm : (l : Layer) (d1 d2 : Direction) : setDir (setDir l d1 .empty) d2 .empty = setDir (setDir l d2 .empty) d1 .empty
L340   theorem    QuarterPos.setQuarter_empty_layers : (s : Shape) (pos : QuarterPos) : (setQuarter s pos .empty).layers = s.layers.set pos.layer (setDir (s.layers.getD pos.layer Layer.empty) pos.dir .empty)
L369   theorem    QuarterPos.layerCount_setQuarter_empty : (s : Shape) (pos : QuarterPos) : (setQuarter s pos .empty).layerCount = s.layerCount
L375   theorem    QuarterPos.setQuarter_empty_comm : (s : Shape) (p q : QuarterPos) : setQuarter (setQuarter s q .empty) p .empty = setQuarter (setQuarter s p .empty) q .empty
L403   theorem    QuarterPos.setQuarter_empty_idem : (s : Shape) (pos : QuarterPos) : setQuarter (setQuarter s pos .empty) pos .empty = setQuarter s pos .empty
L416   theorem    QuarterPos.getDir_setDir_same : (l : Layer) (d : Direction) (q : Quarter) : getDir (setDir l d q) d = q
L421   theorem    QuarterPos.getDir_setDir_ne : (l : Layer) (d1 d2 : Direction) (q : Quarter) (h : d1 ≠ d2) : getDir (setDir l d1 q) d2 = getDir l d2
L427   theorem    QuarterPos.getQuarter_setQuarter_empty_eq : (s : Shape) (pos : QuarterPos) (h_lt : pos.layer < s.layerCount) : getQuarter (setQuarter s pos .empty) pos = some .empty
L436   theorem    QuarterPos.getQuarter_setQuarter_empty_ne : (s : Shape) (pos1 pos2 : QuarterPos) (h : ¬((pos1 == pos2) = true)) : getQuarter (setQuarter s pos1 .empty) pos2 = getQuarter s pos2
L467   theorem    QuarterPos.getQuarter_clearPositions : (s : Shape) (ps : List QuarterPos) (pos : QuarterPos) (h_lt : pos.layer < s.layerCount) : getQuarter (s.clearPositions ps) pos = if ps.any (· == pos) then some .em...
L503   theorem    Shape.layerCount_clearPositions : (s : Shape) (ps : List QuarterPos) : (clearPositions s ps).layerCount = s.layerCount
L512   theorem    Shape.clearPositions_swap : (s : Shape) (p q : QuarterPos) (ps : List QuarterPos) : clearPositions s (p :: q :: ps) = clearPositions s (q :: p :: ps)
L522   theorem    Shape.clearPositions_ext : (s : Shape) (ps1 ps2 : List QuarterPos) (h : ∀ p, ps1.any (· == p) = ps2.any (· == p)) : clearPositions s ps1 = clearPositions s ps2
L548   theorem    Shape.normalize_getQuarter_eq : (s : Shape) (s' : Shape) (h : s.normalize = some s') (p : QuarterPos) (h_valid : p.layer < s'.layerCount) : p.getQuarter s' = p.getQuarter s
L560   theorem    Shape.normalize_nonEmpty_layer_lt : (s : Shape) (s' : Shape) (h_norm : s.normalize = some s') (p : QuarterPos) (q : Quarter) (hq : p.getQuarter s = some q) (hne : q.isEmpty = false) : p.layer < s'....
```
