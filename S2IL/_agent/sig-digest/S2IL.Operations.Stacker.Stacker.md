# S2IL/Operations/Stacker/Stacker.lean

- Lines: 301
- Declarations: 17 (theorems/lemmas: 14, defs/abbrev: 3, private: 1, sorry: 0)

## Landmarks

L10    header    # Stacker (積層機)
L35    namespace Stacker
L138   namespace Shape

## Declarations

```
L43    def        Stacker.placeAbove : (bottom top : Shape) : Shape
L48    theorem    Stacker.placeAbove_layerCount : (bottom top : Shape) : (placeAbove bottom top).layerCount = bottom.layerCount + top.layerCount
L58    def        Stacker.shatterTopCrystals : (s : Shape) (fromLayer : Nat) : Shape
L71    theorem    Stacker.filter_any_eq[priv] : (l : List QuarterPos) (pred : QuarterPos → Bool) (q : QuarterPos) : (l.filter pred).any (· == q) = (l.any (· == q) && pred q)
L95    theorem    Stacker.placeAbove_rotate180 : @[aesop norm simp] theorem placeAbove_rotate180 (bottom top : Shape) : (placeAbove bottom top).rotate180 = placeAbove bottom.rotate180 top.rotate180
L103   theorem    Stacker.shatterTopCrystals_rotate180 : @[aesop norm simp] theorem shatterTopCrystals_rotate180 (s : Shape) (fromLayer : Nat) : (shatterTopCrystals s fromLayer).rotate180 = shatterTopCrystals s.rotate180 fromLayer
L116   theorem    Stacker.placeAbove_rotateCW : @[aesop norm simp] theorem placeAbove_rotateCW (bottom top : Shape) : (placeAbove bottom top).rotateCW = placeAbove bottom.rotateCW top.rotateCW
L124   theorem    Stacker.shatterTopCrystals_rotateCW : @[aesop norm simp] theorem shatterTopCrystals_rotateCW (s : Shape) (fromLayer : Nat) : (shatterTopCrystals s fromLayer).rotateCW = shatterTopCrystals s.rotateCW fromLayer
L148   def        Shape.stack : (bottom top : Shape) (config : GameConfig) : Option Shape
L171   theorem    Shape.truncate_rotate180 : @[aesop norm simp] theorem truncate_rotate180 (s : Shape) (config : GameConfig) : (s.truncate config).rotate180 = s.rotate180.truncate config
L178   theorem    Shape.truncate_rotateCW : @[aesop norm simp] theorem truncate_rotateCW (s : Shape) (config : GameConfig) : (s.truncate config).rotateCW = s.rotateCW.truncate config
L187   theorem    Shape.process_rotate180_placeAbove_settled : (bottom top : Shape) (_h_bottom : bottom.IsSettled) (_h_top : top.IsSettled) : ((Stacker.shatterTopCrystals (Stacker.placeAbove bottom top) bottom.layer...
L197   theorem    Shape.stack_rotate180_comm : (bottom top : Shape) (config : GameConfig) (_h_config : config.maxLayers ≤ 5) (h_bottom : bottom.IsSettled) (h_top : top.IsSettled) : (bottom.stack top config).map Shap...
L225   theorem    Shape.process_rotateCW_placeAbove_settled : (bottom top : Shape) (_h_bottom : bottom.IsSettled) (_h_top : top.IsSettled) : ((Stacker.shatterTopCrystals (Stacker.placeAbove bottom top) bottom.layerC...
L234   theorem    Shape.stack_rotateCW_comm : (bottom top : Shape) (config : GameConfig) (_h_config : config.maxLayers ≤ 5) (h_bottom : bottom.IsSettled) (h_top : top.IsSettled) : (bottom.stack top config).map Shape...
L261   theorem    Shape.stack_rotateCCW_comm : (bottom top : Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) (h_bottom : bottom.IsSettled) (h_top : top.IsSettled) : (bottom.stack top config).map Shape...
L284   theorem    Shape.IsSettled_stack : (bottom top : Shape) (config : GameConfig) (s' : Shape) (h : bottom.stack top config = some s') (h_config : config.maxLayers ≤ 5) : s'.IsSettled
```
