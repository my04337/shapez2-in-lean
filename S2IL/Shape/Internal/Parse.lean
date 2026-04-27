-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types

/-!
# Internal: シェイプコードのパーサ補助

`Shape.ofString?` の実装で使う `:` 分割と非空性補題を提供する。

**外部モジュール（`S2IL/Shape.lean`, `S2IL/Shape/*.lean` 以外）からは import 禁止**。
-/

namespace S2IL.Shape.Internal.Parse

/-- `:` で Char リストを分割する（archive と同じ実装）。
    `[]` の入力は `[[]]` を返す（1 個の空セグメント）。 -/
def splitOnColon : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    if c == ':' then
      [] :: splitOnColon rest
    else
      match splitOnColon rest with
      | [] => [[c]]  -- splitOnColon が空を返さないので unreachable だが、型のため
      | hd :: tl => (c :: hd) :: tl

/-- `:` を含まないリストは `splitOnColon` でシングルトン。 -/
theorem splitOnColon_noColon (cs : List Char) (h : ':' ∉ cs) :
    splitOnColon cs = [cs] := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hc : c ≠ ':' := fun heq => h (heq ▸ .head _)
    have hrest : ':' ∉ rest := fun hi => h (.tail _ hi)
    have h_if : (c == ':') = false := beq_eq_false_iff_ne.mpr hc
    simp only [splitOnColon, h_if, ih hrest, Bool.false_eq_true, ↓reduceIte]

/-- `:` を含まない接頭辞 + `:` :: 後続 の分割。 -/
theorem splitOnColon_append_colon (l1 l2 : List Char) (h : ':' ∉ l1) :
    splitOnColon (l1 ++ ':' :: l2) = l1 :: splitOnColon l2 := by
  induction l1 with
  | nil => simp [splitOnColon]
  | cons c rest ih =>
    have hc : c ≠ ':' := fun heq => h (heq ▸ .head _)
    have hrest : ':' ∉ rest := fun hi => h (.tail _ hi)
    have h_if : (c == ':') = false := beq_eq_false_iff_ne.mpr hc
    simp only [List.cons_append, splitOnColon, h_if, ih hrest,
               Bool.false_eq_true, ↓reduceIte]

/-- `splitOnColon` と `List.intercalate [':']` のラウンドトリップ。 -/
theorem splitOnColon_intercalate
    (lss : List (List Char)) (h_ne : lss ≠ [])
    (h : ∀ cs ∈ lss, ':' ∉ cs) :
    splitOnColon (List.intercalate [':'] lss) = lss := by
  induction lss with
  | nil => exact absurd rfl h_ne
  | cons cs rest ih =>
    cases rest with
    | nil =>
      simp only [List.intercalate, List.intersperse, List.flatten_cons,
                 List.flatten_nil, List.append_nil]
      exact splitOnColon_noColon cs (h cs (.head _))
    | cons cs2 rest2 =>
      have h_rest_ne : cs2 :: rest2 ≠ [] := List.cons_ne_nil _ _
      have hcs : ':' ∉ cs := h cs (.head _)
      have h_rest : ∀ cs' ∈ cs2 :: rest2, ':' ∉ cs' :=
        fun cs' hmem => h cs' (.tail _ hmem)
      have expand : List.intercalate [':'] (cs :: cs2 :: rest2) =
          cs ++ ':' :: List.intercalate [':'] (cs2 :: rest2) := by
        simp [List.intercalate, List.intersperse]
      rw [expand, splitOnColon_append_colon cs _ hcs, ih h_rest_ne h_rest]

end S2IL.Shape.Internal.Parse
