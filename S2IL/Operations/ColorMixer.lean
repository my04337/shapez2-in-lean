-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.ColorMixer

混色機 (A-2-3)。2 つの色を混合する（`Color.mix` のエイリアス）。
-/

namespace S2IL.Operations

/-- 2 色を混合する。 -/
noncomputable def mix (a b : Color) : Color := Color.mix a b

end S2IL.Operations
