# S2IL/Shape/Quarter.lean

- Lines: 104
- Declarations: 9 (theorems/lemmas: 1, defs/abbrev: 7, private: 0, sorry: 0)

## Landmarks

L7     header    # Quarter (象限)
L39    namespace Quarter

## Declarations

```
L28    inductive  Quarter : where
L42    def        Quarter.isEmpty : : Quarter → Bool | empty => true | _ => false / 空とピン以外のシェイプ種別が結合能力を持つ -/ def canFormBond : Quarter → Bool | empty => false | pin => false | crystal _ => true | colored _ _ => true / def...
L48    def        Quarter.canFormBond : : Quarter → Bool | empty => false | pin => false | crystal _ => true | colored _ _ => true / def isFragile : Quarter → Bool | crystal _ => true | _ => false / def partCode? : Quarte...
L55    def        Quarter.isFragile : : Quarter → Bool | crystal _ => true | _ => false / def partCode? : Quarter → Option PartCode | empty => none | pin => some .pin | crystal _ => some .crystal | colored p _ => some p.t...
L60    def        Quarter.partCode? : : Quarter → Option PartCode | empty => none | pin => some .pin | crystal _ => some .crystal | colored p _ => some p.toPartCode / def color? : Quarter → Option Color | colored _ c => s...
L67    def        Quarter.color? : : Quarter → Option Color | colored _ c => some c | crystal c => some c | _ => none / protected def toString : Quarter → String | empty => " | pin => "P-" | crystal c => s!"c{c.toChar}" |...
L73    def        Quarter.toString : : Quarter → String | empty => " | pin => "P-" | crystal c => s!"c{c.toChar}" | colored p c => s!"{p.toChar}{c.toChar}" instance : ToString Quarter where
L83    def        Quarter.ofString? : (s : String) : Option Quarter
L97    theorem    Quarter.ofString_toString : (q : Quarter) : ofString? q.toString = some q
```
