# S2IL/Operations/PinPusher/PinPusher.lean

- Lines: 397
- Declarations: 24 (theorems/lemmas: 21, defs/abbrev: 3, private: 12, sorry: 0)

## Landmarks

L11    header    # PinPusher (ピン押し機)
L31    namespace PinPusher
L107   namespace Shape

## Declarations

```
L38    def        PinPusher.liftUp : (s : Shape) : Shape
L42    theorem    PinPusher.liftUp_layerCount : (s : Shape) : (liftUp s).layerCount = s.layerCount + 1
L51    def        PinPusher.generatePins : (lifted : Shape) (originalBottom : Layer) : Shape
L64    theorem    PinPusher.liftUp_rotate180 : @[aesop norm simp] theorem liftUp_rotate180 (s : Shape) : (liftUp s).rotate180 = liftUp s.rotate180
L74    theorem    PinPusher.generatePins_rotate180 : @[aesop norm simp] theorem generatePins_rotate180 (lifted : Shape) (originalBottom : Layer) : (generatePins lifted originalBottom).rotate180 = generatePins lifted.rotate180 originalBottom.rotate180
L87    theorem    PinPusher.liftUp_rotateCW : @[aesop norm simp] theorem liftUp_rotateCW (s : Shape) : (liftUp s).rotateCW = liftUp s.rotateCW
L97    theorem    PinPusher.generatePins_rotateCW : @[aesop norm simp] theorem generatePins_rotateCW (lifted : Shape) (originalBottom : Layer) : (generatePins lifted originalBottom).rotateCW = generatePins lifted.rotateCW originalBottom.rotateCW
L115   def        Shape.pinPush : (s : Shape) (config : GameConfig) : Option Shape
L137   theorem    Shape.bottom_rotate180[priv] : (s : Shape) : s.rotate180.bottom = s.bottom.rotate180
L143   theorem    Shape.normalize_rotate180[priv] : (s : Shape) : (s.normalize).map Shape.rotate180 = s.rotate180.normalize
L149   theorem    Shape.pinPush_rotate180_comm : @[aesop unsafe 80% apply] theorem pinPush_rotate180_comm (s : Shape) (config : GameConfig) (_h_config : config.maxLayers ≤ 5) : (s.pinPush config).map Shape.rotate180 = s.rotate180.pinPush config
L170   theorem    Shape.bottom_rotateCW[priv] : (s : Shape) : s.rotateCW.bottom = s.bottom.rotateCW
L176   theorem    Shape.normalize_rotateCW[priv] : (s : Shape) : (s.normalize).map Shape.rotateCW = s.rotateCW.normalize
L182   theorem    Shape.pinPush_rotateCW_comm : @[aesop unsafe 80% apply] theorem pinPush_rotateCW_comm (s : Shape) (config : GameConfig) (_h_config : config.maxLayers ≤ 5) : (s.pinPush config).map Shape.rotateCW = s.rotateCW.pinPush config
L204   theorem    Shape.pinPush_rotateCCW_comm : @[aesop unsafe 80% apply] theorem pinPush_rotateCCW_comm (s : Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) : (s.pinPush config).map Shape.rotateCCW = s.rotateCCW.pinPush config
L222   theorem    Shape.decide_isEmpty_eq[priv] : (q : Quarter) : decide (q.isEmpty = true) = q.isEmpty
L227   theorem    Shape.getQuarter_shift[priv] : (s : Shape) (k : Nat) (d : Direction) : QuarterPos.getQuarter (PinPusher.generatePins (PinPusher.liftUp s) s.bottom) ⟨k + 1, d⟩ = QuarterPos.getQuarter s ⟨k, d⟩
L235   theorem    Shape.groundingEdge_shift[priv] : (s : Shape) (a b : QuarterPos) (h : groundingEdge s a b = true) : groundingEdge (PinPusher.generatePins (PinPusher.liftUp s) s.bottom) ⟨a.layer + 1, a.dir⟩ ⟨b.la...
L248   theorem    Shape.reachable_shift[priv] : (s : Shape) (seed p : QuarterPos) (h : GenericReachable (groundingEdge s) seed p) : GenericReachable (groundingEdge (PinPusher.generatePins (PinPusher.liftUp s) s.bo...
L258   theorem    Shape.pin_edge[priv] : (s : Shape) (d : Direction) (q_s : Quarter) (hq_s : QuarterPos.getQuarter s ⟨0, d⟩ = some q_s) (hq_s_ne : q_s.isEmpty = false) : groundingEdge (PinPusher.generatePins (PinP...
L279   theorem    Shape.pin_seed[priv] : (s : Shape) (d : Direction) (q_s : Quarter) (hq_s : QuarterPos.getQuarter s ⟨0, d⟩ = some q_s) (hq_s_ne : q_s.isEmpty = false) : let r
L308   theorem    Shape.IsSettled_liftUp_generatePins[priv] : (s : Shape) (h_settled : s.IsSettled) : (PinPusher.generatePins (PinPusher.liftUp s) s.bottom).IsSettled
L374   theorem    Shape.gravity_eq_normalize_of_settled[priv] : (s : Shape) (h : s.IsSettled) : s.gravity = s.normalize
L382   theorem    Shape.IsSettled_pinPush : (s : Shape) (config : GameConfig) (s' : Shape) (h : s.pinPush config = some s') (h_config : config.maxLayers ≤ 5) (h_settled : s.IsSettled) : s'.IsSettled
```
