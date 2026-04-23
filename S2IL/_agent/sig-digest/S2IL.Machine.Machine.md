# S2IL/Machine/Machine.lean

- Lines: 310
- Declarations: 25 (theorems/lemmas: 14, defs/abbrev: 11, private: 2, sorry: 0)

## Landmarks

L13    header    # Machine (加工装置)
L40    namespace Machine

## Declarations

```
L47    def        Machine.paint : (shape : Option Shape.SettledShape) (color : Option Color) : Option Shape.SettledShape
L58    def        Machine.crystallize : (shape : Option Shape) (color : Option Color) : Option Shape.SettledShape
L68    def        Machine.rotateCW : (shape : Option Shape.SettledShape) : Option Shape.SettledShape
L72    def        Machine.rotateCCW : (shape : Option Shape.SettledShape) : Option Shape.SettledShape
L76    def        Machine.rotate180 : (shape : Option Shape.SettledShape) : Option Shape.SettledShape
L84    def        Machine.pinPush : (shape : Option Shape) (config : GameConfig) : Option Shape
L92    def        Machine.stack : (bottom top : Option Shape) (config : GameConfig) : Option Shape
L102   def        Machine.halfDestroy : (shape : Option Shape) : Option Shape
L113   def        Machine.cut : (shape : Option Shape) : Option Shape × Option Shape
L124   def        Machine.swap : (shape1 shape2 : Option Shape.SettledShape) : Option Shape.SettledShape × Option Shape.SettledShape
L135   def        Machine.mixColor : (color1 color2 : Option Color) : Option Color
L150   theorem    Machine.option_paint_rot_comm[priv] : (rotOut : Shape.SettledShape → Shape.SettledShape) (rotIn : Shape.SettledShape → Shape.SettledShape) (h : ∀ ss c, rotOut (ss.paint c) = (rotIn ss).paint c) (sh...
L167   theorem    Machine.option_crystallize_rot_comm[priv] : (rotOut : Shape.SettledShape → Shape.SettledShape) (rotIn : Shape → Shape) (h : ∀ s c, rotOut (Shape.SettledShape.crystallize s c) = Shape.SettledShape.c...
L183   theorem    Machine.paint_rotateCW_comm : (shape : Option Shape.SettledShape) (color : Option Color) : (paint shape color).map (·.rotateCW) = paint (shape.map (·.rotateCW)) color
L189   theorem    Machine.paint_rotate180_comm : (shape : Option Shape.SettledShape) (color : Option Color) : (paint shape color).map (·.rotate180) = paint (shape.map (·.rotate180)) color
L195   theorem    Machine.paint_rotateCCW_comm : (shape : Option Shape.SettledShape) (color : Option Color) : (paint shape color).map (·.rotateCCW) = paint (shape.map (·.rotateCCW)) color
L201   theorem    Machine.crystallize_rotateCW_comm : (shape : Option Shape) (color : Option Color) : (crystallize shape color).map (·.rotateCW) = crystallize (shape.map Shape.rotateCW) color
L207   theorem    Machine.crystallize_rotate180_comm : (shape : Option Shape) (color : Option Color) : (crystallize shape color).map (·.rotate180) = crystallize (shape.map Shape.rotate180) color
L213   theorem    Machine.crystallize_rotateCCW_comm : (shape : Option Shape) (color : Option Color) : (crystallize shape color).map (·.rotateCCW) = crystallize (shape.map Shape.rotateCCW) color
L223   theorem    Machine.pinPush_rotateCW_comm : (shape : Option Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) : (pinPush shape config).map Shape.rotateCW = pinPush (shape.map Shape.rotateCW) config
L234   theorem    Machine.pinPush_rotate180_comm : (shape : Option Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) : (pinPush shape config).map Shape.rotate180 = pinPush (shape.map Shape.rotate180) config
L245   theorem    Machine.pinPush_rotateCCW_comm : (shape : Option Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) : (pinPush shape config).map Shape.rotateCCW = pinPush (shape.map Shape.rotateCCW) config
L260   theorem    Machine.stack_rotateCW_comm : (bottom top : Option Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) (h_bottom : ∀ s, bottom = some s → s.IsSettled) (h_top : ∀ s, top = some s → s.IsSett...
L277   theorem    Machine.stack_rotate180_comm : (bottom top : Option Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) (h_bottom : ∀ s, bottom = some s → s.IsSettled) (h_top : ∀ s, top = some s → s.IsSet...
L294   theorem    Machine.stack_rotateCCW_comm : (bottom top : Option Shape) (config : GameConfig) (h_config : config.maxLayers ≤ 5) (h_bottom : ∀ s, bottom = some s → s.IsSettled) (h_top : ∀ s, top = some s → s.IsSet...
```
