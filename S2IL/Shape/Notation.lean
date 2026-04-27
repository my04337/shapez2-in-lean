-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types
import S2IL.Shape.Notation.Atom
import S2IL.Shape.Internal.Parse

/-!
# S2IL.Shape.Notation

シェイプコード文字列表現と round-trip 定理（Phase C 完了形）。

## 公開 API

| 種別 | toString | ofString? | round-trip |
|---|---|---|---|
| `Color` | `Color.toChar` | `Color.ofChar?` | `Color.ofChar_toChar` |
| `PartCode` | `.toChar` | `.ofChar?` | `.ofChar_toChar` |
| `RegularPartCode` | `.toChar` | `.ofChar?` | `.ofChar_toChar` |
| `Quarter` | `.toString` (2 chars) | `.ofString?` | `.ofString_toString` |
| `Layer` | `.toString` (8 chars) | `.ofString?` | `.ofString_toString` |
| `Shape` | `.toString` (`:` 区切り) | `.ofString?` | `.ofString_toString`（`IsNormalized` 仮定） |

原子型（Color/PartCode/RegularPartCode）の文字表現は `S2IL.Shape.Notation.Atom`。

## シェイプコード仕様

- Quarter: 2 文字（`--` empty / `P-` pin / `cX` crystal / `XY` colored）
- Layer: 8 文字（NE → SE → SW → NW の順）
- Shape: レイヤを `:` で連結。0 層は空文字列。
-/

namespace S2IL

-- ============================================================
-- Quarter（2 文字表現）
-- ============================================================

namespace Quarter

protected def toString : Quarter → String
  | empty       => "--"
  | pin         => "P-"
  | crystal c   => s!"c{c.toChar}"
  | colored p c => s!"{p.toChar}{c.toChar}"

instance : ToString Quarter := ⟨Quarter.toString⟩

def ofString? (s : String) : Option Quarter :=
  match s.toList with
  | ['-', '-'] => some empty
  | ['P', '-'] => some pin
  | ['c', c1]  =>
    match Color.ofChar? c1 with
    | some c => some (crystal c)
    | none   => none
  | [c0, c1]   =>
    match RegularPartCode.ofChar? c0, Color.ofChar? c1 with
    | some p, some c => some (colored p c)
    | _, _ => none
  | _ => none

theorem ofString_toString (q : Quarter) : ofString? q.toString = some q := by
  cases q with
  | empty => rfl
  | pin => rfl
  | crystal c => cases c <;> rfl
  | colored p c => cases p <;> cases c <;> rfl

end Quarter

-- ============================================================
-- Layer（8 文字表現）
-- ============================================================

namespace Layer

protected def toString (l : Layer) : String :=
  (l 0).toString ++ (l 1).toString ++ (l 2).toString ++ (l 3).toString

instance : ToString Layer := ⟨Layer.toString⟩

def ofString? (s : String) : Option Layer :=
  match s.toList with
  | [a, b, c, d, e, f, g, h] =>
    match Quarter.ofString? (String.ofList [a, b]),
          Quarter.ofString? (String.ofList [c, d]),
          Quarter.ofString? (String.ofList [e, f]),
          Quarter.ofString? (String.ofList [g, h]) with
    | some ne, some se, some sw, some nw => some (Layer.mk ne se sw nw)
    | _, _, _, _ => none
  | _ => none

theorem ofString_toString (l : Layer) : ofString? l.toString = some l := by
  have hQ : ∀ (q : Quarter),
      ∃ a b, q.toString.toList = [a, b] ∧
             Quarter.ofString? (String.ofList [a, b]) = some q := by
    intro q
    cases q with
    | empty => exact ⟨'-', '-', rfl, rfl⟩
    | pin   => exact ⟨'P', '-', rfl, rfl⟩
    | crystal c => cases c <;> exact ⟨_, _, rfl, rfl⟩
    | colored p c => cases p <;> cases c <;> exact ⟨_, _, rfl, rfl⟩
  obtain ⟨a, b, hab, hne⟩ := hQ (l 0)
  obtain ⟨c, d, hcd, hse⟩ := hQ (l 1)
  obtain ⟨e, f, hef, hsw⟩ := hQ (l 2)
  obtain ⟨g, h', hgh, hnw⟩ := hQ (l 3)
  show (ofString? l.toString) = some l
  unfold ofString? Layer.toString
  simp only [String.toList_append, hab, hcd, hef, hgh,
             List.cons_append, List.nil_append, hne, hse, hsw, hnw, mk_eta]

end Layer

-- ============================================================
-- Shape（`:` 区切り）
-- ============================================================

namespace Shape

open S2IL.Shape.Internal.Parse

-- ----- toString の構造補題 -----

private theorem quarter_toString_form (q : Quarter) :
    ∃ a b, q.toString.toList = [a, b] ∧ a ≠ ':' ∧ b ≠ ':' := by
  cases q with
  | empty => exact ⟨'-', '-', rfl, by decide, by decide⟩
  | pin   => exact ⟨'P', '-', rfl, by decide, by decide⟩
  | crystal c => cases c <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | colored p c => cases p <;> cases c <;> exact ⟨_, _, rfl, by decide, by decide⟩

private theorem quarter_toString_noColon (q : Quarter) : ':' ∉ q.toString.toList := by
  obtain ⟨a, b, h, ha, hb⟩ := quarter_toString_form q
  rw [h]; intro hi
  rcases List.mem_cons.mp hi with h | hi
  · exact ha h.symm
  · rcases List.mem_cons.mp hi with h | hi
    · exact hb h.symm
    · exact List.not_mem_nil hi

private theorem quarter_toString_toList_ne_nil (q : Quarter) : q.toString.toList ≠ [] := by
  obtain ⟨a, b, h, _, _⟩ := quarter_toString_form q
  rw [h]; exact List.cons_ne_nil _ _

private theorem layer_toString_noColon (l : Layer) : ':' ∉ l.toString.toList := by
  intro h
  unfold Layer.toString at h
  simp only [String.toList_append, List.mem_append] at h
  rcases h with (((h | h) | h) | h)
  · exact quarter_toString_noColon (l 0) h
  · exact quarter_toString_noColon (l 1) h
  · exact quarter_toString_noColon (l 2) h
  · exact quarter_toString_noColon (l 3) h

private theorem layer_toString_toList_ne_nil (l : Layer) : l.toString.toList ≠ [] := by
  intro h
  unfold Layer.toString at h
  simp only [String.toList_append] at h
  have h1 := (List.append_eq_nil_iff.mp h).1
  have h2 := (List.append_eq_nil_iff.mp h1).1
  have h3 := (List.append_eq_nil_iff.mp h2).1
  exact quarter_toString_toList_ne_nil (l 0) h3

-- ----- パーサ -----

/-- レイヤリストをパースする。いずれか失敗で `none`。 -/
private def parseLayers : List (List Char) → Option (List Layer)
  | [] => some []
  | seg :: rest =>
    match Layer.ofString? (String.ofList seg) with
    | none => none
    | some l =>
      match parseLayers rest with
      | none => none
      | some ls => some (l :: ls)

private theorem parseLayers_map (ls : List Layer) :
    parseLayers (ls.map (fun l => l.toString.toList)) = some ls := by
  induction ls with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.map_cons, parseLayers, String.ofList_toList,
               Layer.ofString_toString, ih]

-- ----- toString / ofString? -----

protected def toString (s : Shape) : String :=
  String.ofList (List.intercalate [':'] (s.map (fun l => l.toString.toList)))

instance : ToString Shape := ⟨Shape.toString⟩

def ofString? (s : String) : Option Shape :=
  let chars := s.toList
  if chars = [] then some []
  else
    match parseLayers (splitOnColon chars) with
    | none    => none
    | some ls => some (normalize ls)

-- ----- round-trip -----

/-- 正規化済みシェイプは `dropTrailingEmpty` で恒等。 -/
private theorem dropTrailingEmpty_of_isNormalized (s : Shape) (h : IsNormalized s) :
    dropTrailingEmpty s = s := by
  unfold dropTrailingEmpty
  cases hs : s.reverse with
  | nil =>
    have : s = [] := by
      have := congrArg List.reverse hs
      simpa using this
    simp [this]
  | cons a rest =>
    have hne : s ≠ [] := by
      intro he; subst he; simp at hs
    have h_last : s.getLast? = some a := by
      have : s = (a :: rest).reverse := by
        have := congrArg List.reverse hs
        simpa using this
      rw [this]
      simp [List.getLast?_reverse]
    have ha : a.isEmpty = false := by
      simp [IsNormalized, h_last, Option.all] at h
      cases hae : a.isEmpty
      · rfl
      · simp [hae] at h
    simp [ha]
    have : (a :: rest).reverse = s := by
      have := congrArg List.reverse hs
      simpa using this.symm
    simpa using this

@[simp] theorem normalize_of_isNormalized (s : Shape) (h : IsNormalized s) :
    normalize s = s := dropTrailingEmpty_of_isNormalized s h

theorem ofString_toString (s : Shape) (h : IsNormalized s) :
    ofString? s.toString = some s := by
  unfold ofString? Shape.toString
  simp only [String.toList_ofList]
  by_cases hs : s = []
  · subst hs; simp [List.intercalate]
  · have h_ne : s.map (fun l => l.toString.toList) ≠ [] :=
      fun he => hs (List.map_eq_nil_iff.mp he)
    have h_noColon : ∀ cs ∈ s.map (fun l => l.toString.toList), ':' ∉ cs := by
      intro cs hcs
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hcs
      exact layer_toString_noColon l
    have h_inter_ne : List.intercalate [':'] (s.map (fun l => l.toString.toList)) ≠ [] := by
      cases hs2 : s with
      | nil => exact absurd hs2 hs
      | cons l rest =>
        intro he
        rw [List.map_cons] at he
        cases rest with
        | nil =>
          simp [List.intercalate] at he
          exact layer_toString_toList_ne_nil l (by simpa using he)
        | cons l2 rest2 =>
          simp [List.intercalate] at he
    rw [if_neg h_inter_ne]
    rw [splitOnColon_intercalate _ h_ne h_noColon, parseLayers_map]
    simp [normalize_of_isNormalized s h]

end Shape

end S2IL
