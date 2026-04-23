# S2IL/Shape/Color.lean

- Lines: 231
- Declarations: 11 (theorems/lemmas: 6, defs/abbrev: 4, private: 0, sorry: 0)

## Landmarks

L4     header    # Color (カラー)
L41    namespace Color
L78    header    ## 混色 (Color Mixing)
L185   header    ## 混色の代数的性質
L205   header    ## 型クラスインスタンス

## Declarations

```
L30    inductive  Color : where
L44    def        Color.toChar : : Color → Char | red => 'r' | green => 'g' | blue => 'b' | yellow => 'y' | cyan => 'c' | magenta => 'm' | white => 'w' | uncolored => 'u' / def ofChar? : Char → Option Color | 'r' => som...
L55    def        Color.ofChar? : : Char → Option Color | 'r' => some red | 'g' => some green | 'b' => some blue | 'y' => some yellow | 'c' => some cyan | 'm' => some magenta | 'w' => some white | 'u' => some uncolored ...
L68    theorem    Color.ofChar_toChar : (c : Color) : ofChar? (toChar c) = some c
L72    def        Color.all : : List Color
L111   def        Color.mix : : Color → Color → Color | red, red => red | red, green => yellow | red, blue => magenta | red, yellow => red | red, cyan => white | red, magenta => red | red, white => red | red, uncolored ...
L190   theorem    Color.mix_comm : (a b : Color) : mix a b = mix b a
L194   theorem    Color.mix_self : @[simp] theorem mix_self (a : Color) : mix a a = a
L198   theorem    Color.mix_uncolored_left : @[simp] theorem mix_uncolored_left (a : Color) : mix uncolored a = a
L202   theorem    Color.mix_uncolored_right : @[simp] theorem mix_uncolored_right (a : Color) : mix a uncolored = a
L228   theorem    Color.mix_not_assoc : : mix (mix red yellow) cyan ≠ mix red (mix yellow cyan)
```
