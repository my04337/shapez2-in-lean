-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel

/-!
# S2IL.Operations.ColorMixer

混色機 (A-2-3)。`Color.mix` の Operations レイヤ alias（Phase D 完了形）。

混色規則の本体は `S2IL.Color.mix`（`Shape/Types/Atom.lean`）にあり、
本 facade では同じ演算を Operations 名前空間に再公開する。

## 公開 API

- `Operations.mix : Color → Color → Color`
- `Operations.mix_comm` / `mix_uncolored_left` / `mix_uncolored_right`

## 単一チェーン原則

混色は Shape 回転と独立な純粋関数（`Color → Color → Color`）。
回転等変性に該当する補題は持たない（Color 自体は回転自由）。
-/

namespace S2IL.Operations

/-- 2 色を混合する。`Color.mix` の Operations レイヤ alias。 -/
def mix (a b : Color) : Color := Color.mix a b

/-- `mix` は可換。 -/
theorem mix_comm (a b : Color) : mix a b = mix b a :=
  Color.mix_comm a b

/-- `mix` は無色を左恒等元として持つ。 -/
@[simp] theorem mix_uncolored_left (a : Color) : mix Color.uncolored a = a :=
  Color.mix_uncolored_left a

/-- `mix` は無色を右恒等元として持つ。 -/
@[simp] theorem mix_uncolored_right (a : Color) : mix a Color.uncolored = a :=
  Color.mix_uncolored_right a

end S2IL.Operations
