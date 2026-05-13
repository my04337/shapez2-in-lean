-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

/-!
# S2IL.Wires.Signal

ワイヤー系 (A-3-1) のシグナル型。現時点では型スケルトンのみ。
-/

namespace S2IL

/-- ワイヤー上を流れるシグナル。 -/
inductive WireSignal where
  /-- 信号なし。 -/
  | off
  /-- 真偽値。 -/
  | boolean (b : Bool)
  /-- シェイプ値。 -/
  | shape (s : Shape)
  /-- 色値。 -/
  | color (c : Color)
  deriving Repr

end S2IL
