# S2IL/Shape/Layer.lean

- Lines: 101
- Declarations: 7 (theorems/lemmas: 2, defs/abbrev: 4, private: 1, sorry: 0)

## Landmarks

L6     header    # Layer (レイヤ)
L43    namespace Layer

## Declarations

```
L32    structure  Layer : where
L46    def        Layer.isEmpty : (l : Layer) : Bool
L50    def        Layer.empty : : Layer
L53    def        Layer.toString : (l : Layer) : String
L60    def        Layer.ofString? : (s : String) : Option Layer
L72    theorem    Layer.ofList_quarter_toList[priv] : (q : Quarter) : String.ofList q.toString.toList = q.toString
L78    theorem    Layer.ofString_toString : (l : Layer) : ofString? l.toString = some l
```
