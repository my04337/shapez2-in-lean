-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.PartCode
import S2IL.Shape.Color
import S2IL.Shape.Quarter
import S2IL.Shape.Layer

/-!
# Shape (シェイプ)

ゲームの主要リソースであるシェイプを表す型。
シェイプは 1 枚以上の **Layer (レイヤ)** を下から上へ積み重ねた構造を持つ。

内部表現は最下層 (`bottom`) と上層レイヤのリスト (`upper`) で構成され、
非空性が構造的に保証される。レイヤ数に制限はない。

シェイプコード記法では、レイヤを `:` で区切り下層から上層の順で記述する。
例: `CuCuCuCu:RrRrRrRr` は下層がサークル(アンカラード)、上層がレクタングル(レッド) の 2 レイヤシェイプ。

> **注記**: 現時点では、空中に浮いたレイヤ等、ゲームシステム上の物理的制約には
> 対応していない。これらは積み重ね・切断などの操作関数を定義する際に考慮する。
-/

/-- シェイプを表す型。1 枚以上のレイヤの積み重ねで構成される。
    `bottom` は最下層、`upper` は上層レイヤのリスト（下から上の順） -/
@[ext]
structure Shape where
    /-- 最下層レイヤ（必ず存在する） -/
    bottom : Layer
    /-- 上層レイヤのリスト（下から上の順） -/
    upper : List Layer
    deriving Repr, DecidableEq, BEq

namespace Shape

-- ============================================================
-- 互換コンストラクタ（旧 API との橋渡し）
-- ============================================================

/-- 1 レイヤのシェイプ -/
@[inline] def single (l1 : Layer) : Shape := ⟨l1, []⟩

/-- 2 レイヤのシェイプ（l1 が下、l2 が上） -/
@[inline] def double (l1 l2 : Layer) : Shape := ⟨l1, [l2]⟩

/-- 3 レイヤのシェイプ（l1 が最下、l3 が最上） -/
@[inline] def triple (l1 l2 l3 : Layer) : Shape := ⟨l1, [l2, l3]⟩

/-- 4 レイヤのシェイプ（l1 が最下、l4 が最上） -/
@[inline] def quadruple (l1 l2 l3 l4 : Layer) : Shape := ⟨l1, [l2, l3, l4]⟩

-- ============================================================
-- 基本操作
-- ============================================================

/-- シェイプのレイヤ数を返す -/
def layerCount (s : Shape) : Nat := s.upper.length + 1

/-- シェイプの全レイヤをリストとして返す（下層から上層の順） -/
def layers (s : Shape) : List Layer := s.bottom :: s.upper

/-- シェイプの最下層レイヤを返す -/
def bottomLayer (s : Shape) : Layer := s.bottom

/-- シェイプの最上層レイヤを返す -/
def topLayer (s : Shape) : Layer :=
    match s.upper.getLast? with
    | some l => l
    | none   => s.bottom

/-- レイヤのリストからシェイプを構築する。空リストの場合は `none` -/
def ofLayers : List Layer → Option Shape
    | []      => none
    | l :: ls => some ⟨l, ls⟩

-- ============================================================
-- 正規化
-- ============================================================

/-- リストの末尾から連続する空レイヤを除去する -/
private def dropTrailingEmpty : List Layer → List Layer
    | [] => []
    | l :: rest =>
        match dropTrailingEmpty rest with
        | [] => if l.isEmpty then [] else [l]
        | kept => l :: kept

/-- シェイプが正規化されている（最上位レイヤが空でない）ことを表す述語 -/
def isNormalized (s : Shape) : Prop :=
    s.topLayer.isEmpty = false

instance : DecidablePred isNormalized := fun s =>
    inferInstanceAs (Decidable (s.topLayer.isEmpty = false))

/-- 末尾の空レイヤをストリップして正規化する。全レイヤが空なら `none` を返す -/
def normalize (s : Shape) : Option Shape :=
    ofLayers (dropTrailingEmpty s.layers)

-- ============================================================
-- 定理
-- ============================================================

/-- `layers` の長さは `layerCount` と等しい -/
theorem layers_length (s : Shape) : s.layers.length = s.layerCount := by
    simp [layers, layerCount]

/-- `layers` は空でない -/
theorem layers_nonempty (s : Shape) : s.layers ≠ [] := by
    simp [layers]

-- ============================================================
-- シリアライズ・デシリアライズ
-- ============================================================

/-- シェイプを Char のリストに変換する（レイヤを `:` 区切りで下層から上層の順に連結） -/
def toCharList (s : Shape) : List Char :=
    let layerChars := s.layers.map (fun l => l.toString.toList)
    List.intercalate [':'] layerChars

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

/-- Char リストのリストから Layer リストへのパース。いずれかが失敗したら none -/
private def parseLayers : List (List Char) → Option (List Layer)
    | [] => some []
    | seg :: rest => do
        let l ← Layer.ofString? (String.ofList seg)
        let ls ← parseLayers rest
        return l :: ls

/-- シェイプコード文字列からシェイプをパースする。
    末尾の空レイヤはストリップされ、全レイヤが空なら `none` を返す。
    レイヤ数に制限はない -/
def ofString? (s : String) : Option Shape := do
    let segments := splitOnColon s.toList
    -- 空の入力は不正
    if segments == [[]] then none
    else
        let layers ← parseLayers segments
        let shape ← ofLayers layers
        shape.normalize

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

/-- 全レイヤの toString → splitOnColon → parseLayers のラウンドトリップ -/
private theorem splitOnColon_intercalate (ls : List Layer) (h : ls ≠ []) :
        splitOnColon (List.intercalate [':'] (ls.map fun l => l.toString.toList))
        = ls.map fun l => l.toString.toList := by
    sorry

/-- parseLayers は Layer.toString.toList のリストに対して元のリストを返す -/
private theorem parseLayers_map_toString (ls : List Layer) :
        parseLayers (ls.map fun l => l.toString.toList) = some ls := by
    induction ls with
    | nil => rfl
    | cons l rest ih =>
        simp only [List.map, parseLayers, Layer.ofString_ofList_toString, ih]
        rfl

/-- dropTrailingEmpty は再帰的に末尾の空レイヤを除去する -/
private theorem dropTrailingEmpty_spec (ls : List Layer) :
        dropTrailingEmpty ls = (ls.reverse.dropWhile Layer.isEmpty).reverse := by
    sorry

/-- 正規化済みのシェイプに `normalize` を適用すると自身を返す -/
theorem normalize_of_isNormalized (s : Shape) (h : s.isNormalized) :
        s.normalize = some s := by
    sorry

/-- `ofString?` と `toString` のラウンドトリップ: 正規化済みのシェイプに対して
    `ofString? (toString s) = some s` が成り立つ -/
theorem ofString_toString (s : Shape) (h : s.isNormalized) :
        ofString? s.toString = some s := by
    sorry

end Shape
