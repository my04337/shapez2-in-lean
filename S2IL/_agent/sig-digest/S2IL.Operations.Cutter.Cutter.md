# S2IL/Operations/Cutter/Cutter.lean

- Lines: 491
- Declarations: 45 (theorems/lemmas: 34, defs/abbrev: 11, private: 7, sorry: 0)

## Landmarks

L9     header    # Cutter (切断)
L58    namespace Layer
L127   namespace Shape

## Declarations

```
L61    def        Layer.eastHalf : (l : Layer) : Layer
L65    def        Layer.westHalf : (l : Layer) : Layer
L70    def        Layer.combineEastWest : (east west : Layer) : Layer
L78    theorem    Layer.combineEastWest_eastHalf_westHalf : (l : Layer) : combineEastWest l.eastHalf l.westHalf = l
L83    theorem    Layer.eastHalf_ne : (l : Layer) : l.eastHalf.ne = l.ne
L84    theorem    Layer.eastHalf_se : (l : Layer) : l.eastHalf.se = l.se
L87    theorem    Layer.westHalf_sw : (l : Layer) : l.westHalf.sw = l.sw
L88    theorem    Layer.westHalf_nw : (l : Layer) : l.westHalf.nw = l.nw
L91    theorem    Layer.eastHalf_sw : (l : Layer) : l.eastHalf.sw = .empty
L92    theorem    Layer.eastHalf_nw : (l : Layer) : l.eastHalf.nw = .empty
L95    theorem    Layer.westHalf_ne : (l : Layer) : l.westHalf.ne = .empty
L96    theorem    Layer.westHalf_se : (l : Layer) : l.westHalf.se = .empty
L99    theorem    Layer.eastHalf_eastHalf : @[simp] theorem eastHalf_eastHalf (l : Layer) : l.eastHalf.eastHalf = l.eastHalf
L103   theorem    Layer.westHalf_westHalf : @[simp] theorem westHalf_westHalf (l : Layer) : l.westHalf.westHalf = l.westHalf
L107   theorem    Layer.eastHalf_rotate180 : @[aesop norm simp] theorem eastHalf_rotate180 (l : Layer) : l.eastHalf.rotate180 = l.rotate180.westHalf
L111   theorem    Layer.westHalf_rotate180 : @[aesop norm simp] theorem westHalf_rotate180 (l : Layer) : l.westHalf.rotate180 = l.rotate180.eastHalf
L116   theorem    Layer.combineEastWest_rotate180 : @[aesop norm simp] theorem combineEastWest_rotate180 (east west : Layer) : (combineEastWest east west).rotate180 = combineEastWest west.rotate180 east.rotate180
L130   def        Shape.eastHalf : (s : Shape) : Shape
L133   def        Shape.westHalf : (s : Shape) : Shape
L140   def        Shape.zipLayersWithPad[priv] : (eastLayers westLayers : List Layer) : List Layer
L151   def        Shape.combineHalves : (east west : Shape) : Shape
L163   def        Shape.settleAfterCut : (s : Shape) : Option Shape
L183   def        Shape.halfDestroy : (s : Shape) : Option Shape
L197   def        Shape.cut : (s : Shape) : Option Shape × Option Shape
L213   def        Shape.swap : (s1 s2 : Shape) : Option Shape × Option Shape
L241   theorem    Shape.zipLayersWithPad_go_eastWest[priv] : (ls : List Layer) : zipLayersWithPad.go (ls.map Layer.eastHalf) (ls.map Layer.westHalf) = ls
L249   theorem    Shape.eastHalf_westHalf_combine : (s : Shape) : combineHalves s.eastHalf s.westHalf = s
L258   theorem    Shape.halfDestroy_eq_cut_east : (s : Shape) : s.halfDestroy = s.cut.1
L263   theorem    Shape.zipLayersWithPad_go_self[priv] : (ls : List Layer) : zipLayersWithPad.go ls ls = ls
L272   theorem    Shape.combineHalves_self : (s : Shape) : combineHalves s s = s
L279   theorem    Shape.zipLayersWithPad_go_rotate180[priv] : (ls1 ls2 : List Layer) : (zipLayersWithPad.go ls1 ls2).map Layer.rotate180 = zipLayersWithPad.go (ls2.map Layer.rotate180) (ls1.map Layer.rotate180)
L303   theorem    Shape.normalize_rotate180[priv] : (s : Shape) : (s.normalize).map Shape.rotate180 = s.rotate180.normalize
L308   theorem    Shape.eastHalf_rotate180 : @[aesop norm simp] theorem eastHalf_rotate180 (s : Shape) : s.eastHalf.rotate180 = s.rotate180.westHalf
L315   theorem    Shape.westHalf_rotate180 : @[aesop norm simp] theorem westHalf_rotate180 (s : Shape) : s.westHalf.rotate180 = s.rotate180.eastHalf
L323   theorem    Shape.settleAfterCut_rotate180[priv] : (s : Shape) (_h : s.layerCount ≤ 5) : (s.settleAfterCut).map Shape.rotate180 = s.rotate180.settleAfterCut
L344   theorem    Shape.cut_eq[priv] : (s : Shape) : s.cut = (s.shatterOnCut.eastHalf.settleAfterCut, s.shatterOnCut.westHalf.settleAfterCut)
L351   theorem    Shape.cut_rotate180_comm : (s : Shape) (h : s.layerCount ≤ 5) : (s.cut.1.map rotate180, s.cut.2.map rotate180) = (s.rotate180.cut.2, s.rotate180.cut.1)
L365   theorem    Shape.swap_self : (s : Shape) : s.swap s = (s.shatterOnCut.settleAfterCut.bind normalize, s.shatterOnCut.settleAfterCut.bind normalize)
L373   theorem    Shape.combineHalves_rotate180 : (a b : Shape) : (combineHalves a b).rotate180 = combineHalves b.rotate180 a.rotate180
L391   theorem    Shape.halfDestroy_rotate180 : (s : Shape) (h : s.layerCount ≤ 5) : (s.halfDestroy).map rotate180 = s.rotate180.cut.2
L404   theorem    Shape.swap_rotate180_comm : (s1 s2 : Shape) (h1 : s1.layerCount ≤ 5) (h2 : s2.layerCount ≤ 5) (hs1 : s1.shatterOnCut.settleAfterCut.isSome = true) (hs2 : s2.shatterOnCut.settleAfterCut.isSome = tru...
L445   theorem    Shape.IsSettled_settleAfterCut : (s : Shape) (s' : Shape) (h : s.settleAfterCut = some s') (h_lc : s.layerCount ≤ 5) : s'.IsSettled
L459   theorem    Shape.IsSettled_halfDestroy : (s : Shape) (s' : Shape) (h : s.halfDestroy = some s') (h_lc : s.layerCount ≤ 5) : s'.IsSettled
L470   theorem    Shape.IsSettled_cut_east : (s : Shape) (s' : Shape) (h : s.cut.1 = some s') (h_lc : s.layerCount ≤ 5) : s'.IsSettled
L477   theorem    Shape.IsSettled_cut_west : (s : Shape) (s' : Shape) (h : s.cut.2 = some s') (h_lc : s.layerCount ≤ 5) : s'.IsSettled
```
