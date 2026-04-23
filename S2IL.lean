-- This module serves as the root of the `S2IL` library.
-- Import modules here that should be built as part of the library.

-- Shape: シェイプ本体の定義
import S2IL.Shape.Shape
import S2IL.Shape.QuarterPos
import S2IL.Shape.GameConfig
import S2IL.Shape.Arbitrary

-- Kernel: 共通理論（Gravity 非依存の横断基盤）
import S2IL.Kernel

-- Operations: 加工操作
import S2IL.Operations

-- SettledShape: 統合型（Operations 統合後のトップレベル）
import S2IL.SettledShape

-- Machine: 加工装置
import S2IL.Machine.Machine
