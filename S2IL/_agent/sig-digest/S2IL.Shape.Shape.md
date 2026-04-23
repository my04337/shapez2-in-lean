# S2IL/Shape/Shape.lean

- Lines: 470
- Declarations: 41 (theorems/lemmas: 21, defs/abbrev: 19, private: 18, sorry: 0)

## Landmarks

L9     header    # Shape (シェイプ)
L36    namespace Shape

## Declarations

```
L30    structure  Shape : where
L59    def        Shape.bottom : (s : Shape) : Layer
L62    def        Shape.upper : (s : Shape) : List Layer
L69    def        Shape.single : @[inline] def single (l1 : Layer) : Shape
L72    def        Shape.double : @[inline] def double (l1 l2 : Layer) : Shape
L75    def        Shape.triple : @[inline] def triple (l1 l2 l3 : Layer) : Shape
L78    def        Shape.quadruple : @[inline] def quadruple (l1 l2 l3 l4 : Layer) : Shape
L85    def        Shape.layerCount : (s : Shape) : Nat
L88    def        Shape.bottomLayer : (s : Shape) : Layer
L91    def        Shape.topLayer : (s : Shape) : Layer
L94    def        Shape.ofLayers : : List Layer → Option Shape | [] => none | l :: ls => some ⟨l :: ls, List.cons_ne_nil l ls⟩ / def mapLayers (s : Shape) (f : Layer → Layer) : Shape where
L103   def        Shape.mapLayers : (s : Shape) (f : Layer → Layer) : Shape where
L112   def        Shape.dropTrailingEmpty[priv] : : List Layer → List Layer | [] => [] | l :: rest => match dropTrailingEmpty rest with | [] => if l.isEmpty then [] else [l] | kept => l :: kept / def isNormalized (s :...
L120   def        Shape.isNormalized : (s : Shape) : Prop
L127   def        Shape.normalize : (s : Shape) : Option Shape
L135   theorem    Shape.dropTrailingEmpty_of_getLast_not_empty[priv] : : ∀ (ls : List Layer) (h : ls ≠ []), (ls.getLast h).isEmpty = false → dropTrailingEmpty ls = ls | [l], _, hl => by have : l.isEmpty = false
L151   theorem    Shape.normalize_of_isNormalized : (s : Shape) (h : s.isNormalized) : s.normalize = some s
L164   theorem    Shape.dropTrailingEmpty_map[priv] : (f : Layer → Layer) (hf : ∀ l, (f l).isEmpty = l.isEmpty) : ∀ (ls : List Layer), (dropTrailingEmpty ls).map f = dropTrailingEmpty (ls.map f) | [] => rfl | l ::...
L183   theorem    Shape.normalize_map_layers : (s : Shape) (f : Layer → Layer) (hf : ∀ l, (f l).isEmpty = l.isEmpty) : (s.normalize).map (Shape.mapLayers · f) = (s.mapLayers f).normalize
L193   theorem    Shape.dropTrailingEmpty_eq_append[priv] : : ∀ (ls : List Layer), ∃ t, ls = (dropTrailingEmpty ls) ++ t | [] => ⟨[], rfl⟩ | l :: rest => by obtain ⟨t, ht⟩
L209   theorem    Shape.normalize_layers_eq_append : (s : Shape) (s' : Shape) (h : s.normalize = some s') : ∃ t, s.layers = s'.layers ++ t
L225   theorem    Shape.dropTrailingEmpty_preserves_nonEmpty_index : (ls : List Layer) (i : Nat) (hi : i < ls.length) (hne : ls[i].isEmpty = false) : i < (dropTrailingEmpty ls).length
L256   theorem    Shape.normalize_preserves_nonEmpty_index : (s : Shape) (s' : Shape) (h : s.normalize = some s') (i : Nat) (h_lt : i < s.layers.length) (h_ne : s.layers[i].isEmpty = false) : i < s'.layerCount
L281   def        Shape.toCharList : (s : Shape) : List Char
L286   def        Shape.toString : (s : Shape) : String
L297   def        Shape.splitOnColon[priv] : : List Char → List (List Char) | [] => [[]] | c :: rest => if c == ':' then [] :: splitOnColon rest else match splitOnColon rest with | [] => [[c]] | hd :: tl => (c :: hd) ...
L308   def        Shape.parseLayers[priv] : : List (List Char) → Option (List Layer) | [] => some [] | seg :: rest => (Layer.ofString? (String.ofList seg)).bind (fun l => (parseLayers rest).bind (fun ls => some (l :: ...
L318   def        Shape.ofString? : (s : String) : Option Shape
L332   theorem    Shape.quarter_toString_noColon[priv] : (q : Quarter) : ':' ∉ q.toString.toList
L340   theorem    Shape.quarter_toString_toList_ne_nil[priv] : (q : Quarter) : q.toString.toList ≠ []
L348   theorem    Shape.layer_toString_noColon[priv] : (l : Layer) : ':' ∉ l.toString.toList
L359   theorem    Shape.layer_toString_toList_ne_nil[priv] : (l : Layer) : l.toString.toList ≠ []
L369   theorem    Shape.splitOnColon_noColon[priv] : (cs : List Char) (h : ':' ∉ cs) : splitOnColon cs = [cs]
L380   theorem    Shape.splitOnColon_append_colon[priv] : (l1 l2 : List Char) (h : ':' ∉ l1) : splitOnColon (l1 ++ ':' :: l2) = l1 :: splitOnColon l2
L391   theorem    Shape.splitOnColon_intercalate[priv] : (lss : List (List Char)) (h_ne : lss ≠ []) (h : ∀ cs ∈ lss, ':' ∉ cs) : splitOnColon (List.intercalate [':'] lss) = lss
L415   theorem    Shape.parseLayers_map_eq[priv] : (ls : List Layer) : parseLayers (ls.map (fun l => l.toString.toList)) = some ls
L424   theorem    Shape.ofLayers_layers[priv] : (s : Shape) : ofLayers s.layers = some s
L434   theorem    Shape.layers_map_toString_ne_nil[priv] : (s : Shape) : s.layers.map (fun l => l.toString.toList) ≠ []
L439   theorem    Shape.layers_map_toString_noColon[priv] : (s : Shape) : ∀ cs ∈ s.layers.map (fun l => l.toString.toList), ':' ∉ cs
L446   theorem    Shape.layers_map_toString_ne_singleton_nil[priv] : (s : Shape) : s.layers.map (fun l => l.toString.toList) ≠ [[]]
L457   theorem    Shape.ofString_toString : (s : Shape) (h : s.isNormalized) : ofString? s.toString = some s
```
