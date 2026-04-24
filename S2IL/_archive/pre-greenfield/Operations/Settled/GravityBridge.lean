-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Operations.Gravity
import S2IL.Operations.Settled.Core

namespace Shape

-- gravity_IsSettled の構成的証明
-- ============================================================
-- 波動モデルでは processWave が floatingUnits = [] まで反復するため、
-- 出力の IsSettled が定義的に導出できる。
-- all_grounded_settle_foldl は foldl モデル固有のため不要。

/-- 落下処理の出力は安定状態である。
    波動モデルにより構成的に証明:
    ① processWave_floatingUnits_empty: processWave の出力は floatingUnits = []
    ② IsSettled_normalize: normalize は floatingUnits = [] を保存する
    ③ ①②の合成で gravity の出力が IsSettled であることが導出される -/
theorem gravity_IsSettled (s : Shape) (s' : Shape) (h : s.gravity = some s')
        (_h_lc : s.layerCount ≤ 5) :
        s'.IsSettled := by
    -- s.gravity = (processWave s).normalize = some s'
    show s'.IsSettled
    have h_pw_settled : (Gravity.processWave s).IsSettled :=
        Gravity.processWave_floatingUnits_empty s
    exact IsSettled_normalize (Gravity.processWave s) s' h h_pw_settled

end Shape
