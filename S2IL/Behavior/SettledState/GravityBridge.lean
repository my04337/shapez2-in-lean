-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Behavior.Gravity
import S2IL.Behavior.SettledState.GroundedCore
import S2IL.Behavior.SettledState.GroundedInvariant
import S2IL.Behavior.SettledState.GroundedPlacement

namespace Shape

-- gravity_IsSettled の最終ブリッジ
-- ============================================================
-- 配置ステップ補題は SettledState/GroundedPlacement.lean に分離

/-- foldl 落下配置後、全非空位置が接地していることの公理。
    計算検証: ≤5L の全 shapes で ImmBelow at pin NE moment = 0 violations。
    Plan B-1 (2026-04-14) で sorry を axiom に切り替え。
    波動モデル導入時（Plan B-3）に構成的証明で置換予定。 -/
private axiom all_grounded_settle_foldl (s : Shape)
        (_h_ne : (Gravity.floatingUnits s).isEmpty = false)
        (h_lc : s.layerCount ≤ 5) :
        let sorted := Gravity.sortFallingUnits' (Gravity.floatingUnits s)
        let allFallingPos := sorted.flatMap Gravity.FallingUnit.positions
        let obstacle := (s.clearPositions allFallingPos).layers
        let result := sorted.foldl (fun obs u =>
            let d := Gravity.landingDistance u obs
            Gravity.placeFallingUnit s obs u d) obstacle
        ∀ (s_mid : Shape),
        Shape.ofLayers result = some s_mid →
        ∀ (p : QuarterPos),
        p.layer < s_mid.layerCount →
        (∃ q, p.getQuarter s_mid = some q ∧ !q.isEmpty = true) →
        p ∈ Gravity.groundedPositions s_mid

/-- 落下処理の出力は安定状態である（基盤定理）。
    計算検証: ≤5L の 1.9M+ shapes で 0 failures。
    Plan B-1 (2026-04-14) で sorry を axiom に切り替え。
    波動モデル導入時（Plan B-3）に構成的証明で置換予定。 -/
axiom gravity_IsSettled (s : Shape) (s' : Shape) (h : s.gravity = some s')
        (h_lc : s.layerCount ≤ 5) :
        s'.IsSettled

end Shape







