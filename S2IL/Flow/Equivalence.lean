-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Defs

/-!
# S2IL.Flow.Equivalence

Flow の外延的等価性。

構造同値やグラフ同型ではなく、`Flow.eval` の入力出力が一致することを正本にする。
-/

namespace S2IL
namespace Flow

variable {α β γ δ : Type 0}

/-- 2 つのフローが全入力で同じ出力を返すこと。 -/
def Equivalent (leftFlow rightFlow : Flow α β) : Prop :=
  ∀ input, Flow.eval leftFlow input = Flow.eval rightFlow input

/-- Flow 等価性の反射律。 -/
theorem Equivalent.refl (flow : Flow α β) : Equivalent flow flow := by
  intro input
  rfl

/-- Flow 等価性の対称律。 -/
theorem Equivalent.symm {leftFlow rightFlow : Flow α β}
    (equivalent : Equivalent leftFlow rightFlow) : Equivalent rightFlow leftFlow := by
  intro input
  exact (equivalent input).symm

/-- Flow 等価性の推移律。 -/
theorem Equivalent.trans {firstFlow secondFlow thirdFlow : Flow α β}
    (equivalentFirst : Equivalent firstFlow secondFlow)
    (equivalentSecond : Equivalent secondFlow thirdFlow) :
    Equivalent firstFlow thirdFlow := by
  intro input
  exact Eq.trans (equivalentFirst input) (equivalentSecond input)

/-- 合成に対する Flow 等価性の congruence。 -/
theorem Equivalent.comp {firstLeft firstRight : Flow α β} {secondLeft secondRight : Flow β γ}
    (equivalentFirst : Equivalent firstLeft firstRight)
    (equivalentSecond : Equivalent secondLeft secondRight) :
    Equivalent (Flow.comp firstLeft secondLeft) (Flow.comp firstRight secondRight) := by
  intro input
  change Flow.eval secondLeft (Flow.eval firstLeft input) =
    Flow.eval secondRight (Flow.eval firstRight input)
  rw [equivalentFirst input]
  exact equivalentSecond (Flow.eval firstRight input)

/-- 合成の前段だけを置き換える congruence。 -/
theorem Equivalent.comp_left {firstLeft firstRight : Flow α β} (secondFlow : Flow β γ)
    (equivalent : Equivalent firstLeft firstRight) :
    Equivalent (Flow.comp firstLeft secondFlow) (Flow.comp firstRight secondFlow) :=
  Equivalent.comp equivalent (Equivalent.refl secondFlow)

/-- 合成の後段だけを置き換える congruence。 -/
theorem Equivalent.comp_right (firstFlow : Flow α β) {secondLeft secondRight : Flow β γ}
    (equivalent : Equivalent secondLeft secondRight) :
    Equivalent (Flow.comp firstFlow secondLeft) (Flow.comp firstFlow secondRight) :=
  Equivalent.comp (Equivalent.refl firstFlow) equivalent

/-- 左単位律: `id` を前段に合成しても外延的に変わらない。 -/
theorem Equivalent.id_left (flow : Flow α β) :
    Equivalent (Flow.comp Flow.id flow) flow := by
  intro input
  rfl

/-- 右単位律: `id` を後段に合成しても外延的に変わらない。 -/
theorem Equivalent.id_right (flow : Flow α β) :
    Equivalent (Flow.comp flow Flow.id) flow := by
  intro input
  rfl

/-- ペア第 1 成分への適用に対する Flow 等価性の congruence。 -/
theorem Equivalent.first {leftFlow rightFlow : Flow α β}
    (equivalent : Equivalent leftFlow rightFlow) :
    Equivalent (Flow.first leftFlow : Flow (α × γ) (β × γ)) (Flow.first rightFlow) := by
  intro input
  cases input with
  | mk firstValue secondValue =>
    change (Flow.eval leftFlow firstValue, secondValue) =
      (Flow.eval rightFlow firstValue, secondValue)
    rw [equivalent firstValue]

/-- ペア第 2 成分への適用に対する Flow 等価性の congruence。 -/
theorem Equivalent.second {leftFlow rightFlow : Flow α β}
    (equivalent : Equivalent leftFlow rightFlow) :
    Equivalent (Flow.second leftFlow : Flow (γ × α) (γ × β)) (Flow.second rightFlow) := by
  intro input
  cases input with
  | mk firstValue secondValue =>
    change (firstValue, Flow.eval leftFlow secondValue) =
      (firstValue, Flow.eval rightFlow secondValue)
    rw [equivalent secondValue]

/-- fanout に対する Flow 等価性の congruence。 -/
theorem Equivalent.fanout {leftFirst rightFirst : Flow α β} {leftSecond rightSecond : Flow α γ}
    (equivalentFirst : Equivalent leftFirst rightFirst)
    (equivalentSecond : Equivalent leftSecond rightSecond) :
    Equivalent (Flow.fanout leftFirst leftSecond) (Flow.fanout rightFirst rightSecond) := by
  intro input
  change (Flow.eval leftFirst input, Flow.eval leftSecond input) =
    (Flow.eval rightFirst input, Flow.eval rightSecond input)
  rw [equivalentFirst input, equivalentSecond input]

/-- `pairMap` に対する Flow 等価性の congruence。 -/
theorem Equivalent.pairMap {leftFirst rightFirst : Flow α β} {leftSecond rightSecond : Flow γ δ}
    (equivalentFirst : Equivalent leftFirst rightFirst)
    (equivalentSecond : Equivalent leftSecond rightSecond) :
    Equivalent (Flow.pairMap leftFirst leftSecond) (Flow.pairMap rightFirst rightSecond) :=
  Equivalent.comp (Equivalent.first equivalentFirst) (Equivalent.second equivalentSecond)

/-- product の右結合化と左結合化を順に行うと外延的に元へ戻る。 -/
theorem Equivalent.assocRight_assocLeft :
    Equivalent
      (Flow.comp (Flow.assocRight : Flow ((α × β) × γ) (α × (β × γ))) Flow.assocLeft)
      (Flow.id : Flow ((α × β) × γ) ((α × β) × γ)) := by
  intro input
  cases input with
  | mk pair thirdValue =>
    cases pair with
    | mk firstValue secondValue => rfl

/-- product の左結合化と右結合化を順に行うと外延的に元へ戻る。 -/
theorem Equivalent.assocLeft_assocRight :
    Equivalent
      (Flow.comp (Flow.assocLeft : Flow (α × (β × γ)) ((α × β) × γ)) Flow.assocRight)
      (Flow.id : Flow (α × (β × γ)) (α × (β × γ))) := by
  intro input
  cases input with
  | mk firstValue pair =>
    cases pair with
    | mk secondValue thirdValue => rfl

end Flow
end S2IL
