-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.PartCode
import S2IL.Shape.Color
import S2IL.Shape.Quarter
import S2IL.Shape.Layer

/-!
# Shape (シェイプ)

ゲームの主要リソースであるシェイプを表す型。
シェイプは 1〜4 枚の **Layer (レイヤ)** を下から上へ積み重ねた構造を持つ。

各コンストラクタはレイヤ数に対応し、引数は下層 (`l1`) から上層へ向かう順序で並ぶ。
シェイプコード記法では、レイヤを `:` で区切り下層から上層の順で記述する。
例: `CuCuCuCu:RrRrRrRr` は下層がサークル(アンカラード)、上層がレクタングル(レッド) の 2 レイヤシェイプ。

> **注記**: 現時点では、空中に浮いたレイヤ等、ゲームシステム上の物理的制約には
> 対応していない。これらは積み重ね・切断などの操作関数を定義する際に考慮する。
-/

/-- シェイプを表す型。1〜4 レイヤの積み重ねで構成される -/
inductive Shape where
    /-- 1 レイヤのシェイプ -/
    | single (l1 : Layer)
    /-- 2 レイヤのシェイプ（l1 が下、l2 が上） -/
    | double (l1 l2 : Layer)
    /-- 3 レイヤのシェイプ（l1 が最下、l3 が最上） -/
    | triple (l1 l2 l3 : Layer)
    /-- 4 レイヤのシェイプ（l1 が最下、l4 が最上） -/
    | quadruple (l1 l2 l3 l4 : Layer)
    deriving Repr, DecidableEq, BEq

namespace Shape

/-- シェイプのレイヤ数を返す -/
def layerCount : Shape → Nat
    | single ..    => 1
    | double ..    => 2
    | triple ..    => 3
    | quadruple .. => 4

/-- シェイプの全レイヤをリストとして返す（下層から上層の順） -/
def layers : Shape → List Layer
    | single l1           => [l1]
    | double l1 l2        => [l1, l2]
    | triple l1 l2 l3     => [l1, l2, l3]
    | quadruple l1 l2 l3 l4 => [l1, l2, l3, l4]

/-- シェイプの最下層レイヤを返す -/
def bottomLayer : Shape → Layer
    | single l1
    | double l1 _
    | triple l1 _ _
    | quadruple l1 _ _ _ => l1

/-- シェイプの最上層レイヤを返す -/
def topLayer : Shape → Layer
    | single l1            => l1
    | double _ l2          => l2
    | triple _ _ l3        => l3
    | quadruple _ _ _ l4   => l4

/-- シェイプが正規化されている（最上位レイヤが空でない）ことを表す述語 -/
def isNormalized : Shape → Prop
    | single l1            => l1.isEmpty = false
    | double _ l2          => l2.isEmpty = false
    | triple _ _ l3        => l3.isEmpty = false
    | quadruple _ _ _ l4   => l4.isEmpty = false

instance : DecidablePred isNormalized := fun s =>
    match s with
    | single l1            => inferInstanceAs (Decidable (l1.isEmpty = false))
    | double _ l2          => inferInstanceAs (Decidable (l2.isEmpty = false))
    | triple _ _ l3        => inferInstanceAs (Decidable (l3.isEmpty = false))
    | quadruple _ _ _ l4   => inferInstanceAs (Decidable (l4.isEmpty = false))

/-- 末尾の空レイヤをストリップして正規化する。全レイヤが空なら `none` を返す -/
def normalize : Shape → Option Shape
    | single l1 =>
        if l1.isEmpty then none else some (single l1)
    | double l1 l2 =>
        if l2.isEmpty then
            if l1.isEmpty then none else some (single l1)
        else some (double l1 l2)
    | triple l1 l2 l3 =>
        if l3.isEmpty then
            if l2.isEmpty then
                if l1.isEmpty then none else some (single l1)
            else some (double l1 l2)
        else some (triple l1 l2 l3)
    | quadruple l1 l2 l3 l4 =>
        if l4.isEmpty then
            if l3.isEmpty then
                if l2.isEmpty then
                    if l1.isEmpty then none else some (single l1)
                else some (double l1 l2)
            else some (triple l1 l2 l3)
        else some (quadruple l1 l2 l3 l4)

/-- `layers` の長さは `layerCount` と等しい -/
theorem layers_length (s : Shape) : s.layers.length = s.layerCount := by
    cases s <;> rfl

/-- `layers` は空でない -/
theorem layers_nonempty (s : Shape) : s.layers ≠ [] := by
    cases s <;> simp [layers]

/-- シェイプを Char のリストに変換する（レイヤを `:` 区切りで下層から上層の順に連結） -/
def toCharList : Shape → List Char
    | single l1 => l1.toString.toList
    | double l1 l2 =>
        l1.toString.toList ++ ':' :: l2.toString.toList
    | triple l1 l2 l3 =>
        l1.toString.toList ++ ':' :: (l2.toString.toList ++ ':' :: l3.toString.toList)
    | quadruple l1 l2 l3 l4 =>
        l1.toString.toList ++ ':' :: (l2.toString.toList ++ ':' ::
        (l3.toString.toList ++ ':' :: l4.toString.toList))

/-- シェイプをシェイプコード文字列に変換する -/
protected def toString (s : Shape) : String :=
    String.ofList s.toCharList

instance : ToString Shape where
    toString := Shape.toString

-- ============================================================
-- ofString? のための内部ヘルパー
-- ============================================================

/-- `:` で Char のリストを分割する -/
private def splitOnColon : List Char → List (List Char)
    | [] => [[]]
    | c :: rest =>
        if c == ':' then
            [] :: splitOnColon rest
        else
            match splitOnColon rest with
            | [] => [[c]]
            | hd :: tl => (c :: hd) :: tl

/-- シェイプコード文字列からシェイプをパースする。
    末尾の空レイヤはストリップされ、全レイヤが空なら `none` を返す -/
def ofString? (s : String) : Option Shape :=
    match splitOnColon s.toList with
    | [c1] =>
        match Layer.ofString? (String.ofList c1) with
        | some l1 => (single l1).normalize
        | none => none
    | [c1, c2] =>
        match Layer.ofString? (String.ofList c1),
              Layer.ofString? (String.ofList c2) with
        | some l1, some l2 => (double l1 l2).normalize
        | _, _ => none
    | [c1, c2, c3] =>
        match Layer.ofString? (String.ofList c1),
              Layer.ofString? (String.ofList c2),
              Layer.ofString? (String.ofList c3) with
        | some l1, some l2, some l3 => (triple l1 l2 l3).normalize
        | _, _, _ => none
    | [c1, c2, c3, c4] =>
        match Layer.ofString? (String.ofList c1),
              Layer.ofString? (String.ofList c2),
              Layer.ofString? (String.ofList c3),
              Layer.ofString? (String.ofList c4) with
        | some l1, some l2, some l3, some l4 => (quadruple l1 l2 l3 l4).normalize
        | _, _, _, _ => none
    | _ => none

-- ============================================================
-- ofString_toString の証明に必要な補助定理
-- ============================================================

/-- Quarter.toString の各文字が `:` でないこと -/
private theorem Quarter.toString_noColon (q : Quarter) :
        ':' ∉ q.toString.toList := by
    cases q with
    | empty => decide
    | pin => decide
    | crystal c => cases c <;> decide
    | colored p c => cases p <;> cases c <;> decide

/-- Layer.toString が `:` を含まないこと -/
private theorem Layer.toString_noColon (l : Layer) :
        ':' ∉ l.toString.toList := by
    simp only [Layer.toString, String.toList_append, List.mem_append]
    intro h
    rcases h with ((h | h) | h) | h
    · exact Quarter.toString_noColon l.ne h
    · exact Quarter.toString_noColon l.se h
    · exact Quarter.toString_noColon l.sw h
    · exact Quarter.toString_noColon l.nw h

/-- `:` を含まないリストに対する splitOnColon -/
private theorem splitOnColon_noColon (cs : List Char) (h : ':' ∉ cs) :
        splitOnColon cs = [cs] := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
        have hc : c ≠ ':' := by intro heq; exact h (heq ▸ .head _)
        have hrest : ':' ∉ rest := by intro hmem; exact h (.tail _ hmem)
        simp only [splitOnColon, beq_iff_eq, hc, ite_false, ih hrest]

/-- L1 ++ ':' :: L2 に対する splitOnColon -/
private theorem splitOnColon_append_colon (l1 l2 : List Char) (h1 : ':' ∉ l1) :
        splitOnColon (l1 ++ ':' :: l2) = l1 :: splitOnColon l2 := by
    induction l1 with
    | nil => simp [splitOnColon]
    | cons c rest ih =>
        have hc : c ≠ ':' := by intro heq; exact h1 (heq ▸ .head _)
        have hrest : ':' ∉ rest := by intro hmem; exact h1 (.tail _ hmem)
        simp only [List.cons_append, splitOnColon, beq_iff_eq, hc, ite_false, ih hrest]

/-- Layer.ofString? (String.ofList l.toString.toList) = some l -/
private theorem Layer.ofString_ofList_toString (l : Layer) :
        Layer.ofString? (String.ofList l.toString.toList) = some l := by
    rw [String.ofList_toList]
    exact Layer.ofString_toString l

/-- 正規化済みのシェイプに `normalize` を適用すると自身を返す -/
theorem normalize_of_isNormalized (s : Shape) (h : s.isNormalized) :
        s.normalize = some s := by
    cases s with
    | single l1 =>
        simp only [isNormalized] at h
        simp [normalize, h]
    | double _ l2 =>
        simp only [isNormalized] at h
        simp [normalize, h]
    | triple _ _ l3 =>
        simp only [isNormalized] at h
        simp [normalize, h]
    | quadruple _ _ _ l4 =>
        simp only [isNormalized] at h
        simp [normalize, h]

/-- `ofString?` と `toString` の一般版ラウンドトリップ:
    `ofString? (toString s) = s.normalize` -/
theorem ofString_toString_normalize (s : Shape) :
        ofString? s.toString = s.normalize := by
    simp only [ofString?, Shape.toString, String.toList_ofList]
    cases s with
    | single l1 =>
        rw [toCharList, splitOnColon_noColon _ (Layer.toString_noColon l1)]
        simp only [Layer.ofString_ofList_toString]
    | double l1 l2 =>
        rw [toCharList, splitOnColon_append_colon _ _ (Layer.toString_noColon l1),
            splitOnColon_noColon _ (Layer.toString_noColon l2)]
        simp only [Layer.ofString_ofList_toString]
    | triple l1 l2 l3 =>
        rw [toCharList, splitOnColon_append_colon _ _ (Layer.toString_noColon l1),
            splitOnColon_append_colon _ _ (Layer.toString_noColon l2),
            splitOnColon_noColon _ (Layer.toString_noColon l3)]
        simp only [Layer.ofString_ofList_toString]
    | quadruple l1 l2 l3 l4 =>
        rw [toCharList, splitOnColon_append_colon _ _ (Layer.toString_noColon l1),
            splitOnColon_append_colon _ _ (Layer.toString_noColon l2),
            splitOnColon_append_colon _ _ (Layer.toString_noColon l3),
            splitOnColon_noColon _ (Layer.toString_noColon l4)]
        simp only [Layer.ofString_ofList_toString]

/-- `ofString?` と `toString` のラウンドトリップ: 正規化済みのシェイプに対して
    `ofString? (toString s) = some s` が成り立つ -/
theorem ofString_toString (s : Shape) (h : s.isNormalized) :
        ofString? s.toString = some s := by
    rw [ofString_toString_normalize]
    exact normalize_of_isNormalized s h

end Shape
