# S2IL/Operations/Painter/Painter.lean

- Lines: 114
- Declarations: 14 (theorems/lemmas: 11, defs/abbrev: 3, private: 0, sorry: 0)

## Landmarks

L8     header    # Painter (着色機)
L24    namespace Painter
L75    namespace Shape

## Declarations

```
L27    def        Painter.paintQuarter : (q : Quarter) (color : Color) : Quarter
L33    def        Painter.paintLayer : (l : Layer) (color : Color) : Layer
L42    theorem    Painter.paintQuarter_empty : (color : Color) : paintQuarter .empty color = .empty
L46    theorem    Painter.paintQuarter_pin : (color : Color) : paintQuarter .pin color = .pin
L50    theorem    Painter.paintQuarter_crystal : (c color : Color) : paintQuarter (.crystal c) color = .crystal c
L54    theorem    Painter.paintQuarter_idempotent : @[simp] theorem paintQuarter_idempotent (q : Quarter) (color : Color) : paintQuarter (paintQuarter q color) color = paintQuarter q color
L59    theorem    Painter.paintLayer_idempotent : @[simp] theorem paintLayer_idempotent (l : Layer) (color : Color) : paintLayer (paintLayer l color) color = paintLayer l color
L64    theorem    Painter.paintLayer_rotate180 : @[aesop norm simp] theorem paintLayer_rotate180 (l : Layer) (color : Color) : (paintLayer l color).rotate180 = paintLayer l.rotate180 color
L69    theorem    Painter.paintLayer_rotateCW : @[aesop norm simp] theorem paintLayer_rotateCW (l : Layer) (color : Color) : (paintLayer l color).rotateCW = paintLayer l.rotateCW color
L78    def        Shape.paint : (s : Shape) (color : Color) : Shape
L89    theorem    Shape.paint_idempotent : @[simp] theorem paint_idempotent (s : Shape) (color : Color) : (s.paint color).paint color = s.paint color
L96    theorem    Shape.paint_rotateCW_comm : @[aesop norm simp] theorem paint_rotateCW_comm (s : Shape) (color : Color) : (s.paint color).rotateCW = (s.rotateCW).paint color
L105   theorem    Shape.paint_rotate180_comm : @[aesop norm simp] theorem paint_rotate180_comm (s : Shape) (color : Color) : (s.paint color).rotate180 = (s.rotate180).paint color
L110   theorem    Shape.paint_rotateCCW_comm : @[aesop norm simp] theorem paint_rotateCCW_comm (s : Shape) (color : Color) : (s.paint color).rotateCCW = (s.rotateCCW).paint color
```
