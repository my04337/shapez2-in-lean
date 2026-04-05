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

内部表現はレイヤのリスト (`layers`) と非空性の証明 (`layers_ne`) で構成され、
非空性が型レベルで保証される。`List` API をそのまま利用できるため
証明の展開ステップが少なく、`@[ext]` は `layers` の等価性のみで
シェイプの等価性を導出する（`layers_ne` は `Prop` なので proof irrelevance）。

シェイプコード記法では、レイヤを `:` で区切り下層から上層の順で記述する。
例: `CuCuCuCu:RrRrRrRr` は下層がサークル(アンカラード)、上層がレクタングル(レッド) の 2 レイヤシェイプ。

> **注記**: 現時点では、空中に浮いたレイヤ等、ゲームシステム上の物理的制約には
> 対応していない。これらは積み重ね・切断などの操作関数を定義する際に考慮する。
-/

/-- シェイプを表す型。1 枚以上のレイヤの積み重ねで構成される。
    `layers` はレイヤのリスト（下層から上層の順）、`layers_ne` は非空性の証明 -/
@[ext]
structure Shape where
    /-- レイヤのリスト（下層から上層の順、非空） -/
    layers : List Layer
    /-- レイヤリストが空でないことの証明 -/
    layers_ne : layers ≠ []

namespace Shape

-- ============================================================
-- 手動 deriving（Prop フィールドを含む構造体のため）
-- ============================================================

instance : Repr Shape where
    reprPrec s n := reprPrec s.layers n

instance : DecidableEq Shape := fun s1 s2 =>
    if h : s1.layers = s2.layers then
        isTrue (Shape.ext h)
    else
        isFalse (fun heq => h (heq ▸ rfl))

instance : BEq Shape where
    beq s1 s2 := s1.layers == s2.layers

-- ============================================================
-- 互換アクセサ（旧 API との橋渡し）
-- ============================================================

/-- 最下層レイヤを返す（旧 `bottom` フィールド互換） -/
def bottom (s : Shape) : Layer := s.layers.head s.layers_ne

/-- 上層レイヤのリストを返す（旧 `upper` フィールド互換） -/
def upper (s : Shape) : List Layer := s.layers.tail

-- ============================================================
-- コンストラクタ
-- ============================================================

/-- 1 レイヤのシェイプ -/
@[inline] def single (l1 : Layer) : Shape := ⟨[l1], by simp only [ne_eq, List.cons_ne_self, not_false_eq_true]⟩

/-- 2 レイヤのシェイプ（l1 が下、l2 が上） -/
@[inline] def double (l1 l2 : Layer) : Shape := ⟨[l1, l2], by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

/-- 3 レイヤのシェイプ（l1 が最下、l3 が最上） -/
@[inline] def triple (l1 l2 l3 : Layer) : Shape := ⟨[l1, l2, l3], by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

/-- 4 レイヤのシェイプ（l1 が最下、l4 が最上） -/
@[inline] def quadruple (l1 l2 l3 l4 : Layer) : Shape := ⟨[l1, l2, l3, l4], by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

-- ============================================================
-- 基本操作
-- ============================================================

/-- シェイプのレイヤ数を返す -/
def layerCount (s : Shape) : Nat := s.layers.length

/-- シェイプの最下層レイヤを返す -/
def bottomLayer (s : Shape) : Layer := s.layers.head s.layers_ne

/-- シェイプの最上層レイヤを返す -/
def topLayer (s : Shape) : Layer := s.layers.getLast s.layers_ne

/-- レイヤのリストからシェイプを構築する。空リストの場合は `none` -/
def ofLayers : List Layer → Option Shape
    | []      => none
    | l :: ls => some ⟨l :: ls, List.cons_ne_nil l ls⟩

-- ============================================================
-- レイヤ操作ユーティリティ
-- ============================================================

private theorem map_ne_nil_of_ne_nil (l : List Layer) (f : Layer → Layer)
        (h : l ≠ []) : l.map f ≠ [] := by
    cases l with
    | nil => exact h
    | cons _ _ => exact List.cons_ne_nil _ _

/-- 全レイヤに関数を適用する -/
def mapLayers (s : Shape) (f : Layer → Layer) : Shape where
    layers := s.layers.map f
    layers_ne := map_ne_nil_of_ne_nil s.layers f s.layers_ne

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

/-- 最後の要素が空でないリストに対し、`dropTrailingEmpty` は恒等写像 -/
private theorem dropTrailingEmpty_of_getLast_not_empty :
        ∀ (ls : List Layer) (h : ls ≠ []),
        (ls.getLast h).isEmpty = false → dropTrailingEmpty ls = ls
    | [l], _, hl => by
        have : l.isEmpty = false := hl
        unfold dropTrailingEmpty dropTrailingEmpty
        simp only [this, Bool.false_eq_true, ↓reduceIte]
    | l :: r :: rest, _, hl => by
        have h_ne : r :: rest ≠ [] := List.cons_ne_nil r rest
        have h_last : ((r :: rest).getLast h_ne).isEmpty = false := by
            rwa [List.getLast_cons h_ne] at hl
        show dropTrailingEmpty (l :: r :: rest) = l :: r :: rest
        unfold dropTrailingEmpty
        rw [dropTrailingEmpty_of_getLast_not_empty (r :: rest) h_ne h_last]

/-- 正規化済みのシェイプに `normalize` を適用すると自身を返す -/
theorem normalize_of_isNormalized (s : Shape) (h : s.isNormalized) :
        s.normalize = some s := by
    simp only [normalize, isNormalized, topLayer] at *
    rw [dropTrailingEmpty_of_getLast_not_empty s.layers s.layers_ne h]
    have ⟨a, as, hl⟩ : ∃ a as, s.layers = a :: as := by
        cases hc : s.layers with
        | nil => exact absurd hc s.layers_ne
        | cons a as => exact ⟨a, as, rfl⟩
    rw [hl]
    simp only [ofLayers]
    exact congrArg some (Shape.ext hl.symm)

/-- isEmpty を保存する写像に対して dropTrailingEmpty は map と可換 -/
private theorem dropTrailingEmpty_map (f : Layer → Layer)
        (hf : ∀ l, (f l).isEmpty = l.isEmpty) :
        ∀ (ls : List Layer),
        (dropTrailingEmpty ls).map f = dropTrailingEmpty (ls.map f)
    | [] => rfl
    | l :: rest => by
        have ih := dropTrailingEmpty_map f hf rest
        show (match dropTrailingEmpty rest with
              | [] => if l.isEmpty then [] else [l]
              | kept => l :: kept).map f =
             (match dropTrailingEmpty (List.map f rest) with
              | [] => if (f l).isEmpty then [] else [f l]
              | kept => f l :: kept)
        rw [← ih]
        cases dropTrailingEmpty rest with
        | nil => rw [hf l]; cases l.isEmpty <;> rfl
        | cons _ _ => simp only [List.map]

/-- isEmpty を保存する写像で mapLayers した結果の normalize は可換 -/
theorem normalize_map_layers (s : Shape) (f : Layer → Layer)
        (hf : ∀ l, (f l).isEmpty = l.isEmpty) :
        (s.normalize).map (Shape.mapLayers · f) = (s.mapLayers f).normalize := by
    simp only [normalize, mapLayers]
    rw [← dropTrailingEmpty_map f hf s.layers]
    cases dropTrailingEmpty s.layers with
    | nil => rfl
    | cons a as => simp only [ofLayers, Option.map_some, List.map_cons]

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
    | seg :: rest =>
        (Layer.ofString? (String.ofList seg)).bind (fun l =>
        (parseLayers rest).bind (fun ls =>
        some (l :: ls)))

/-- シェイプコード文字列からシェイプをパースする。
    末尾の空レイヤはストリップされ、全レイヤが空なら `none` を返す。
    レイヤ数に制限はない -/
def ofString? (s : String) : Option Shape :=
    let segments := splitOnColon s.toList
    -- 空の入力は不正
    if segments == [[]] then none
    else
        (parseLayers segments).bind (fun parsedLayers =>
        (ofLayers parsedLayers).bind (fun shape =>
        shape.normalize))

-- ============================================================
-- ofString_toString の証明に必要な補助定理
-- ============================================================

/-- `Quarter.toString` に `:` が含まれないことの証明 -/
private theorem quarter_toString_noColon (q : Quarter) : ':' ∉ q.toString.toList := by
    cases q with
    | empty => decide
    | pin => decide
    | crystal c => cases c <;> decide
    | colored p c => cases p <;> cases c <;> decide

/-- `Quarter.toString.toList` が空でないことの証明 -/
private theorem quarter_toString_toList_ne_nil (q : Quarter) : q.toString.toList ≠ [] := by
    cases q with
    | empty => decide
    | pin => decide
    | crystal c => cases c <;> decide
    | colored p c => cases p <;> cases c <;> decide

/-- `Layer.toString` に `:` が含まれないことの証明 -/
private theorem layer_toString_noColon (l : Layer) : ':' ∉ l.toString.toList := by
    intro h
    unfold Layer.toString at h
    simp only [String.toList_append, List.mem_append] at h
    rcases h with (((h1 | h2) | h3) | h4)
    · exact quarter_toString_noColon l.ne h1
    · exact quarter_toString_noColon l.se h2
    · exact quarter_toString_noColon l.sw h3
    · exact quarter_toString_noColon l.nw h4

/-- `Layer.toString.toList` が空でないことの証明 -/
private theorem layer_toString_toList_ne_nil (l : Layer) : l.toString.toList ≠ [] := by
    intro h
    unfold Layer.toString at h
    simp only [String.toList_append] at h
    have h1 := (List.append_eq_nil_iff.mp h).1
    have h2 := (List.append_eq_nil_iff.mp h1).1
    have h3 := (List.append_eq_nil_iff.mp h2).1
    exact quarter_toString_toList_ne_nil l.ne h3

/-- `:` を含まないリストは `splitOnColon` でシングルトンリストになる -/
private theorem splitOnColon_noColon (cs : List Char) (h : ':' ∉ cs) :
        splitOnColon cs = [cs] := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
        have hc : c ≠ ':' := fun heq => h (heq ▸ .head _)
        have hrest : ':' ∉ rest := fun hi => h (.tail _ hi)
        have h_if : (c == ':') = false := beq_eq_false_iff_ne.mpr hc
        simp only [splitOnColon, h_if, ih hrest]; simp only [Bool.false_eq_true, ↓reduceIte]

/-- `:` を含まない接頭辞に `:` :: 後続を追加した場合の `splitOnColon` -/
private theorem splitOnColon_append_colon (l1 l2 : List Char) (h : ':' ∉ l1) :
        splitOnColon (l1 ++ ':' :: l2) = l1 :: splitOnColon l2 := by
    induction l1 with
    | nil => simp only [↓Char.isValue, List.nil_append, splitOnColon, BEq.rfl, ↓reduceIte]
    | cons c rest ih =>
        have hc : c ≠ ':' := fun heq => h (heq ▸ .head _)
        have hrest : ':' ∉ rest := fun hi => h (.tail _ hi)
        have h_if : (c == ':') = false := beq_eq_false_iff_ne.mpr hc
        simp only [List.cons_append, splitOnColon, h_if, ih hrest]; simp only [Bool.false_eq_true, ↓reduceIte]

/-- `splitOnColon` と `List.intercalate [':']` のラウンドトリップ -/
private theorem splitOnColon_intercalate
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
                simp only [List.intercalate, List.intersperse, List.flatten_cons,
                           List.cons_append, List.nil_append]
            rw [expand, splitOnColon_append_colon cs _ hcs, ih h_rest_ne h_rest]

/-- `parseLayers (ls.map (fun l => l.toString.toList)) = some ls` -/
private theorem parseLayers_map_eq (ls : List Layer) :
        parseLayers (ls.map (fun l => l.toString.toList)) = some ls := by
    induction ls with
    | nil => simp only [List.map_nil, parseLayers]
    | cons l rest ih =>
        simp only [List.map_cons, parseLayers, String.ofList_toList,
                   Layer.ofString_toString, Option.bind_some, ih]

/-- `ofLayers s.layers = some s` -/
private theorem ofLayers_layers (s : Shape) : ofLayers s.layers = some s := by
    cases hc : s.layers with
    | nil => exact absurd hc s.layers_ne
    | cons l ls =>
        simp only [ofLayers]
        exact congrArg some (Shape.ext hc.symm)

/-- `ofString?` と `toString` のラウンドトリップ: 正規化済みのシェイプに対して
    `ofString? (toString s) = some s` が成り立つ -/
theorem ofString_toString (s : Shape) (h : s.isNormalized) :
        ofString? s.toString = some s := by
    -- toString を展開して List Char レベルに落とす
    simp only [ofString?, Shape.toString, String.toList_ofList, toCharList]
    -- splitOnColon (intercalate ':' layers.map f) = layers.map f を適用
    have h_ne : s.layers.map (fun l => l.toString.toList) ≠ [] :=
        fun h_e => s.layers_ne (List.map_eq_nil_iff.mp h_e)
    have h_nc : ∀ cs ∈ s.layers.map (fun l => l.toString.toList), ':' ∉ cs := by
        intro cs hcs
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp hcs
        exact layer_toString_noColon l
    rw [splitOnColon_intercalate _ h_ne h_nc]
    -- 分割結果が [[]] でないことを示す（Layer.toString は常に 8 文字）
    have h_ne_cc : s.layers.map (fun l => l.toString.toList) ≠ [[]] := by
        cases hc : s.layers with
        | nil => exact absurd hc s.layers_ne
        | cons l ls =>
            rw [List.map_cons]
            intro h_eq
            exact layer_toString_toList_ne_nil l (List.cons.inj h_eq).1
    -- Bool の if 条件を false に簡約（false = true は False に変換してから if_false を適用）
    have h_beq : (s.layers.map (fun l => l.toString.toList) == [[]]) = false :=
        beq_eq_false_iff_ne.mpr h_ne_cc
    simp only [h_beq, Bool.false_eq_true, if_false]
    -- parseLayers、ofLayers、normalize の順に計算
    rw [parseLayers_map_eq]
    simp only [Option.bind_some]
    rw [ofLayers_layers]
    simp only [Option.bind_some]
    exact normalize_of_isNormalized s h

end Shape
