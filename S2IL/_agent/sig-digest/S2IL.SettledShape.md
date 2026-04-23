# S2IL/SettledShape.lean

- Lines: 179
- Declarations: 14 (theorems/lemmas: 2, defs/abbrev: 12, private: 2, sorry: 0)

## Landmarks

L11    header    # SettledShape の操作と Arbitrary インスタンス
L36    namespace Shape.SettledShape

## Declarations

```
L43    def        Shape.SettledShape.paint : (ss : SettledShape) (c : Color) : SettledShape
L48    def        Shape.SettledShape.crystallize : (s : Shape) (c : Color) : SettledShape
L52    def        Shape.SettledShape.rotateCW : (ss : SettledShape) : SettledShape
L56    def        Shape.SettledShape.rotateCCW : (ss : SettledShape) : SettledShape
L60    def        Shape.SettledShape.gravity : (s : Shape) (h_lc : s.layerCount ≤ 5) : Option SettledShape
L66    def        Shape.SettledShape.pinPush : (ss : SettledShape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) : Option SettledShape
L73    def        Shape.SettledShape.stack : (bottom top : SettledShape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) : Option SettledShape
L80    def        Shape.SettledShape.cut : (s : Shape) (h_lc : s.layerCount ≤ 5) : Option SettledShape × Option SettledShape
L90    def        Shape.SettledShape.halfDestroy : (s : Shape) (h_lc : s.layerCount ≤ 5) : Option SettledShape
L96    def        Shape.SettledShape.toSettledOption[priv] : (os : Option Shape) : Option SettledShape
L105   def        Shape.SettledShape.swap : (ss1 ss2 : SettledShape) : Option SettledShape × Option SettledShape
L114   theorem    Shape.SettledShape.eq_of_val_eq : {ss1 ss2 : SettledShape} (h : ss1.val = ss2.val) : ss1 = ss2
L118   theorem    Shape.SettledShape.val_eq_of_eq : {ss1 ss2 : SettledShape} (h : ss1 = ss2) : ss1.val = ss2.val
L152   def        Shape.SettledShape.settledShapeGen[priv] : : Gen SettledShape
```
