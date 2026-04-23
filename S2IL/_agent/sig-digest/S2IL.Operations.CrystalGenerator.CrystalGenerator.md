# S2IL/Operations/CrystalGenerator/CrystalGenerator.lean

- Lines: 113
- Declarations: 13 (theorems/lemmas: 10, defs/abbrev: 3, private: 0, sorry: 0)

## Landmarks

L8     header    # CrystalGenerator (結晶製造機)
L27    namespace CrystalGenerator
L75    namespace Shape

## Declarations

```
L30    def        CrystalGenerator.fillQuarter : (q : Quarter) (color : Color) : Quarter
L37    def        CrystalGenerator.fillLayer : (l : Layer) (color : Color) : Layer
L46    theorem    CrystalGenerator.fillQuarter_colored : (p : RegularPartCode) (c color : Color) : fillQuarter (.colored p c) color = .colored p c
L50    theorem    CrystalGenerator.fillQuarter_crystal : (c color : Color) : fillQuarter (.crystal c) color = .crystal c
L54    theorem    CrystalGenerator.fillQuarter_idempotent : @[simp] theorem fillQuarter_idempotent (q : Quarter) (color : Color) : fillQuarter (fillQuarter q color) color = fillQuarter q color
L59    theorem    CrystalGenerator.fillLayer_idempotent : @[simp] theorem fillLayer_idempotent (l : Layer) (color : Color) : fillLayer (fillLayer l color) color = fillLayer l color
L64    theorem    CrystalGenerator.fillLayer_rotate180 : @[aesop norm simp] theorem fillLayer_rotate180 (l : Layer) (color : Color) : (fillLayer l color).rotate180 = fillLayer l.rotate180 color
L69    theorem    CrystalGenerator.fillLayer_rotateCW : @[aesop norm simp] theorem fillLayer_rotateCW (l : Layer) (color : Color) : (fillLayer l color).rotateCW = fillLayer l.rotateCW color
L78    def        Shape.crystallize : (s : Shape) (color : Color) : Shape
L86    theorem    Shape.crystallize_idempotent : @[simp] theorem crystallize_idempotent (s : Shape) (color : Color) : (s.crystallize color).crystallize color = s.crystallize color
L92    theorem    Shape.crystallize_rotateCW_comm : @[aesop norm simp] theorem crystallize_rotateCW_comm (s : Shape) (color : Color) : (s.crystallize color).rotateCW = (s.rotateCW).crystallize color
L104   theorem    Shape.crystallize_rotate180_comm : @[aesop norm simp] theorem crystallize_rotate180_comm (s : Shape) (color : Color) : (s.crystallize color).rotate180 = (s.rotate180).crystallize color
L109   theorem    Shape.crystallize_rotateCCW_comm : @[aesop norm simp] theorem crystallize_rotateCCW_comm (s : Shape) (color : Color) : (s.crystallize color).rotateCCW = (s.rotateCCW).crystallize color
```
