-- This module serves as the root of the `S2IL` library.
-- Import modules here that should be built as part of the library.

-- Shape: シェイプ本体の定義
import S2IL.Shape.Shape
import S2IL.Shape.QuarterPos
import S2IL.Shape.GameConfig

-- Behavior: シェイプの振る舞い
import S2IL.Behavior.Rotate
import S2IL.Behavior.GenericBfs
import S2IL.Behavior.CrystalBond
import S2IL.Behavior.Rotate180Lemmas
import S2IL.Behavior.Shatter
import S2IL.Behavior.Gravity
import S2IL.Behavior.Stacker
import S2IL.Behavior.PinPusher
import S2IL.Behavior.CrystalGenerator
import S2IL.Behavior.Painter
import S2IL.Behavior.Cutter
import S2IL.Behavior.ColorMixer

-- Machine: 加工装置
import S2IL.Machine.Machine
