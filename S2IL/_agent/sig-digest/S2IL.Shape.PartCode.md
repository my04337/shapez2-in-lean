# S2IL/Shape/PartCode.lean

- Lines: 147
- Declarations: 13 (theorems/lemmas: 3, defs/abbrev: 8, private: 0, sorry: 0)

## Landmarks

L4     header    # Part Code (パーツコード)
L36    namespace PartCode
L71    header    # Regular Part Code (通常パーツコード)
L98    namespace RegularPartCode

## Declarations

```
L27    inductive  PartCode : where
L39    def        PartCode.toChar : : PartCode → Char | circle => 'C' | rectangle => 'R' | star => 'S' | windmill => 'W' | pin => 'P' | crystal => 'c' / def ofChar? : Char → Option PartCode | 'C' => some circle | 'R' => so...
L48    def        PartCode.ofChar? : : Char → Option PartCode | 'C' => some circle | 'R' => some rectangle | 'S' => some star | 'W' => some windmill | 'P' => some pin | 'c' => some crystal | _ => none / `ofChar? (toChar p)...
L59    theorem    PartCode.ofChar_toChar : (p : PartCode) : ofChar? (toChar p) = some p
L63    def        PartCode.all : : List PartCode
L91    inductive  RegularPartCode : where
L101   def        RegularPartCode.toChar : : RegularPartCode → Char | circle => 'C' | rectangle => 'R' | star => 'S' | windmill => 'W' / def ofChar? : Char → Option RegularPartCode | 'C' => some circle | 'R' => some rectangle | '...
L108   def        RegularPartCode.ofChar? : : Char → Option RegularPartCode | 'C' => some circle | 'R' => some rectangle | 'S' => some star | 'W' => some windmill | _ => none / `ofChar? (toChar p) = some p` が成り立つ -/ theorem ofCha...
L117   theorem    RegularPartCode.ofChar_toChar : (p : RegularPartCode) : ofChar? (toChar p) = some p
L121   def        RegularPartCode.toPartCode : : RegularPartCode → PartCode | circle => .circle | rectangle => .rectangle | star => .star | windmill => .windmill / def ofPartCode? : PartCode → Option RegularPartCode | .circle => ...
L128   def        RegularPartCode.ofPartCode? : : PartCode → Option RegularPartCode | .circle => some circle | .rectangle => some rectangle | .star => some star | .windmill => some windmill | .pin => none | .crystal => none / the...
L137   theorem    RegularPartCode.ofPartCode_toPartCode : (p : RegularPartCode) : ofPartCode? (toPartCode p) = some p
L141   def        RegularPartCode.all : : List RegularPartCode
```
