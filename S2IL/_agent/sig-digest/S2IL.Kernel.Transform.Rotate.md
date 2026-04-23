# S2IL/Kernel/Transform/Rotate.lean

- Lines: 241
- Declarations: 33 (theorems/lemmas: 27, defs/abbrev: 6, private: 0, sorry: 0)

## Landmarks

L6     header    # Rotate (回転)
L38    namespace Layer
L149   namespace Shape

## Declarations

```
L51    def        Layer.rotateCW : (l : Layer) : Layer
L57    def        Layer.rotateCCW : (l : Layer) : Layer
L63    def        Layer.rotate180 : (l : Layer) : Layer
L71    theorem    Layer.rotateCCW_eq_rotateCW_rotateCW_rotateCW : (l : Layer) : l.rotateCCW = l.rotateCW.rotateCW.rotateCW
L75    theorem    Layer.rotate180_eq_rotateCW_rotateCW : (l : Layer) : l.rotate180 = l.rotateCW.rotateCW
L79    theorem    Layer.rotateCW_four : @[simp] theorem rotateCW_four (l : Layer) : l.rotateCW.rotateCW.rotateCW.rotateCW = l
L84    theorem    Layer.rotateCCW_rotateCW : @[simp] theorem rotateCCW_rotateCW (l : Layer) : l.rotateCCW.rotateCW = l
L89    theorem    Layer.rotateCW_rotateCCW : @[simp] theorem rotateCW_rotateCCW (l : Layer) : l.rotateCW.rotateCCW = l
L94    theorem    Layer.rotate180_rotate180 : @[simp] theorem rotate180_rotate180 (l : Layer) : l.rotate180.rotate180 = l
L99    theorem    Layer.rotateCCW_four : @[simp] theorem rotateCCW_four (l : Layer) : l.rotateCCW.rotateCCW.rotateCCW.rotateCCW = l
L104   theorem    Layer.rotateCW_rotate180_comm : @[simp] theorem rotateCW_rotate180_comm (l : Layer) : l.rotateCW.rotate180 = l.rotate180.rotateCW
L109   theorem    Layer.rotateCCW_rotate180_comm : @[simp] theorem rotateCCW_rotate180_comm (l : Layer) : l.rotateCCW.rotate180 = l.rotate180.rotateCCW
L114   theorem    Layer.rotateCW_rotateCCW_comm : (l : Layer) : l.rotateCW.rotateCCW = l.rotateCCW.rotateCW
L119   theorem    Layer.rotate180_eq_rotateCCW_rotateCCW : (l : Layer) : l.rotate180 = l.rotateCCW.rotateCCW
L124   theorem    Layer.rotateCW_three_eq_rotateCCW : (l : Layer) : l.rotateCW.rotateCW.rotateCW = l.rotateCCW
L129   theorem    Layer.isEmpty_rotateCW : @[simp] theorem isEmpty_rotateCW (l : Layer) : l.rotateCW.isEmpty = l.isEmpty
L134   theorem    Layer.isEmpty_rotateCCW : @[simp] theorem isEmpty_rotateCCW (l : Layer) : l.rotateCCW.isEmpty = l.isEmpty
L139   theorem    Layer.isEmpty_rotate180 : @[simp] theorem isEmpty_rotate180 (l : Layer) : l.rotate180.isEmpty = l.isEmpty
L154   def        Shape.rotateCW : (s : Shape) : Shape
L159   def        Shape.rotateCCW : (s : Shape) : Shape
L164   def        Shape.rotate180 : (s : Shape) : Shape
L171   theorem    Shape.rotateCCW_eq_rotateCW_rotateCW_rotateCW : (s : Shape) : s.rotateCCW = s.rotateCW.rotateCW.rotateCW
L178   theorem    Shape.rotate180_eq_rotateCW_rotateCW : (s : Shape) : s.rotate180 = s.rotateCW.rotateCW
L185   theorem    Shape.rotateCW_four : @[simp] theorem rotateCW_four (s : Shape) : s.rotateCW.rotateCW.rotateCW.rotateCW = s
L191   theorem    Shape.rotateCCW_rotateCW : @[simp] theorem rotateCCW_rotateCW (s : Shape) : s.rotateCCW.rotateCW = s
L197   theorem    Shape.rotateCW_rotateCCW : @[simp] theorem rotateCW_rotateCCW (s : Shape) : s.rotateCW.rotateCCW = s
L203   theorem    Shape.rotate180_rotate180 : @[simp] theorem rotate180_rotate180 (s : Shape) : s.rotate180.rotate180 = s
L209   theorem    Shape.rotateCCW_four : @[simp] theorem rotateCCW_four (s : Shape) : s.rotateCCW.rotateCCW.rotateCCW.rotateCCW = s
L215   theorem    Shape.rotateCW_rotate180_comm : @[simp] theorem rotateCW_rotate180_comm (s : Shape) : s.rotateCW.rotate180 = s.rotate180.rotateCW
L221   theorem    Shape.rotateCCW_rotate180_comm : @[simp] theorem rotateCCW_rotate180_comm (s : Shape) : s.rotateCCW.rotate180 = s.rotate180.rotateCCW
L227   theorem    Shape.layerCount_rotateCW : @[simp] theorem layerCount_rotateCW (s : Shape) : s.rotateCW.layerCount = s.layerCount
L232   theorem    Shape.layerCount_rotateCCW : @[simp] theorem layerCount_rotateCCW (s : Shape) : s.rotateCCW.layerCount = s.layerCount
L237   theorem    Shape.layerCount_rotate180 : @[simp] theorem layerCount_rotate180 (s : Shape) : s.rotate180.layerCount = s.layerCount
```
