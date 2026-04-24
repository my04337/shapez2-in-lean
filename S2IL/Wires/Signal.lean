-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape

/-!
# S2IL.Wires.Signal

ワイヤー系 (A-3-1) のシグナル型。Phase B は型スケルトンのみ。
-/

namespace S2IL

/-- ワイヤー上を流れるシグナル。 -/
axiom WireSignal : Type

namespace WireSignal
axiom off : WireSignal
axiom boolean : Bool → WireSignal
axiom shape : Shape → WireSignal
axiom color : Color → WireSignal
end WireSignal

end S2IL
