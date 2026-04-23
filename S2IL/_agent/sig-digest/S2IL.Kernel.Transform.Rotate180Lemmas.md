# S2IL/Kernel/Transform/Rotate180Lemmas.lean

- Lines: 286
- Declarations: 26 (theorems/lemmas: 23, defs/abbrev: 2, private: 0, sorry: 0)

## Landmarks

L8     header    # 回転等変性の共通補題
L86    namespace LayerPerm
L123   namespace QuarterPos
L153   namespace Shape
L171   namespace QuarterPos
L260   namespace Shape

## Declarations

```
L27    structure  LayerPerm : where
L57    abbrev     LayerPerm.rotate180 : : LayerPerm where
L70    abbrev     LayerPerm.rotateCW : : LayerPerm where
L89    theorem    LayerPerm.quarterPos_beq : (σ : LayerPerm) (p q : QuarterPos) : (σ.onQPos p == σ.onQPos q) = (p == q)
L96    theorem    LayerPerm.list_any_map : (σ : LayerPerm) (l : List QuarterPos) (p : QuarterPos) : (l.map σ.onQPos).any (· == σ.onQPos p) = l.any (· == p)
L103   theorem    LayerPerm.list_any_cons : (σ : LayerPerm) (x : QuarterPos) (l : List QuarterPos) (p : QuarterPos) : ((σ.onQPos x :: l.map σ.onQPos).any (· == σ.onQPos p)) = ((x :: l).any (· == p))
L110   theorem    LayerPerm.onDir_injective : (σ : LayerPerm) {d1 d2 : Direction} (h : σ.onDir d1 = σ.onDir d2) : d1 = d2
L126   theorem    QuarterPos.getDir_rotate180 : @[aesop norm simp] theorem getDir_rotate180 (l : Layer) (d : Direction) : getDir (l.rotate180) (d.rotate180) = getDir l d
L131   theorem    QuarterPos.getDir_rotateCW : @[aesop norm simp] theorem getDir_rotateCW (l : Layer) (d : Direction) : getDir (l.rotateCW) (d.rotateCW) = getDir l d
L136   theorem    QuarterPos.setDir_rotate180_empty : @[aesop norm simp] theorem setDir_rotate180_empty (l : Layer) (d : Direction) : (setDir l d .empty).rotate180 = setDir (l.rotate180) (d.rotate180) .empty
L142   theorem    QuarterPos.setDir_rotateCW_empty : @[aesop norm simp] theorem setDir_rotateCW_empty (l : Layer) (d : Direction) : (setDir l d .empty).rotateCW = setDir (l.rotateCW) (d.rotateCW) .empty
L156   theorem    Shape.layers_rotate180 : @[aesop norm simp] theorem layers_rotate180 (s : Shape) : s.rotate180.layers = s.layers.map Layer.rotate180
L161   theorem    Shape.layers_rotateCW : @[aesop norm simp] theorem layers_rotateCW (s : Shape) : s.rotateCW.layers = s.layers.map Layer.rotateCW
L174   theorem    QuarterPos.getQuarter_perm : (σ : LayerPerm) (s : Shape) (p : QuarterPos) : (σ.onQPos p).getQuarter (s.mapLayers σ.onLayer) = p.getQuarter s
L183   theorem    QuarterPos.getQuarter_rotate180 : @[aesop norm simp] theorem getQuarter_rotate180 (s : Shape) (pos : QuarterPos) : pos.rotate180.getQuarter s.rotate180 = pos.getQuarter s
L188   theorem    QuarterPos.getQuarter_rotateCW : @[aesop norm simp] theorem getQuarter_rotateCW (s : Shape) (pos : QuarterPos) : pos.rotateCW.getQuarter s.rotateCW = pos.getQuarter s
L194   theorem    QuarterPos.getQuarter_perm_inv : (σ : LayerPerm) (s : Shape) (p : QuarterPos) : p.getQuarter (s.mapLayers σ.onLayer) = (σ.onQPosInv p).getQuarter s
L200   theorem    QuarterPos.getQuarter_rotate180_inv : @[aesop norm simp] theorem getQuarter_rotate180_inv (s : Shape) (p : QuarterPos) : p.getQuarter s.rotate180 = p.rotate180.getQuarter s
L205   theorem    QuarterPos.getQuarter_rotateCW_inv : @[aesop norm simp] theorem getQuarter_rotateCW_inv (s : Shape) (p : QuarterPos) : p.getQuarter s.rotateCW = p.rotateCCW.getQuarter s
L214   theorem    QuarterPos.setQuarter_layers_eq : (s : Shape) (pos : QuarterPos) (q : Quarter) (l : Layer) (hl : s.layers[pos.layer]? = some l) : (pos.setQuarter s q).layers = s.layers.set pos.layer (setDir l pos.dir q)
L224   theorem    QuarterPos.setQuarter_perm_empty : (σ : LayerPerm) (s : Shape) (pos : QuarterPos) : (pos.setQuarter s .empty).mapLayers σ.onLayer = (σ.onQPos pos).setQuarter (s.mapLayers σ.onLayer) .empty
L245   theorem    QuarterPos.setQuarter_rotate180_empty : @[aesop norm simp] theorem setQuarter_rotate180_empty (s : Shape) (pos : QuarterPos) : (pos.setQuarter s .empty).rotate180 = (pos.rotate180).setQuarter (s.rotate180) .empty
L250   theorem    QuarterPos.setQuarter_rotateCW_empty : @[aesop norm simp] theorem setQuarter_rotateCW_empty (s : Shape) (pos : QuarterPos) : (pos.setQuarter s .empty).rotateCW = (pos.rotateCW).setQuarter (s.rotateCW) .empty
L263   theorem    Shape.clearPositions_perm : (σ : LayerPerm) (s : Shape) (ps : List QuarterPos) : (s.clearPositions ps).mapLayers σ.onLayer = (s.mapLayers σ.onLayer).clearPositions (ps.map σ.onQPos)
L275   theorem    Shape.clearPositions_rotate180 : @[aesop norm simp] theorem clearPositions_rotate180 (s : Shape) (ps : List QuarterPos) : (s.clearPositions ps).rotate180 = (s.rotate180).clearPositions (ps.map QuarterPos.rotate180)
L281   theorem    Shape.clearPositions_rotateCW : @[aesop norm simp] theorem clearPositions_rotateCW (s : Shape) (ps : List QuarterPos) : (s.clearPositions ps).rotateCW = (s.rotateCW).clearPositions (ps.map QuarterPos.rotateCW)
```
