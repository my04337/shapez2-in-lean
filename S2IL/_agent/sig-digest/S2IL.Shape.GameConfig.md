# S2IL/Shape/GameConfig.lean

- Lines: 111
- Declarations: 10 (theorems/lemmas: 4, defs/abbrev: 5, private: 1, sorry: 0)

## Landmarks

L6     header    # GameConfig (ゲーム設定)
L56    namespace GameConfig
L76    namespace Shape

## Declarations

```
L44    def        myConfig : : GameConfig
L50    structure  GameConfig : where
L59    def        GameConfig.vanilla4 : : GameConfig where
L64    def        GameConfig.vanilla5 : : GameConfig where
L70    def        GameConfig.stress8 : : GameConfig where
L79    theorem    Shape.take_ne_nil_of_ne_nil_pos[priv] : (l : List α) (n : Nat) (hl : l ≠ []) (hn : 0 < n) : l.take n ≠ []
L89    def        Shape.truncate : (s : Shape) (config : GameConfig) : Shape where
L94    theorem    Shape.truncate_layerCount_le : (s : Shape) (config : GameConfig) : (s.truncate config).layerCount ≤ config.maxLayers
L100   theorem    Shape.truncate_of_le : (s : Shape) (config : GameConfig) (h : s.layerCount ≤ config.maxLayers) : s.truncate config = s
L107   theorem    Shape.truncate_idempotent : @[simp] theorem truncate_idempotent (s : Shape) (config : GameConfig) : (s.truncate config).truncate config = s.truncate config
```
