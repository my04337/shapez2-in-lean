import S2IL.Shape.Types.Layer

/-!
# S2IL.Shape.Types.Shape

`Shape := List Layer` と shape 基本操作。
-/

namespace S2IL

/-- シェイプ。0 枚以上のレイヤを下から積み重ねた構造（`List Layer`）。 -/
abbrev Shape := List Layer

namespace Shape

/-- 0 層シェイプ（空）。 -/
def empty : Shape := []

/-- 識別関数（旧 API 互換）。 -/
def layers (s : Shape) : List Layer := s

/-- レイヤ数。 -/
def layerCount (s : Shape) : Nat := s.length

def single     (l1 : Layer)                 : Shape := [l1]
def double     (l1 l2 : Layer)              : Shape := [l1, l2]
def triple     (l1 l2 l3 : Layer)           : Shape := [l1, l2, l3]
def quadruple  (l1 l2 l3 l4 : Layer)        : Shape := [l1, l2, l3, l4]

/-- 最下層レイヤ（0 層なら空レイヤ）。 -/
def bottomLayer (s : Shape) : Layer :=
  s.head?.getD Layer.empty

/-- 最上層レイヤ（0 層なら空レイヤ）。 -/
def topLayer (s : Shape) : Layer :=
  s.getLast?.getD Layer.empty

/-- 各レイヤに関数を適用。 -/
def mapLayers (s : Shape) (f : Layer → Layer) : Shape := s.map f

-- ----------------------
-- 正規化（§1.11 規約）
-- ----------------------

/-- 末尾から連続する空レイヤを除去する補助関数。
    `reverse + dropWhile + reverse` で簡潔に実装する。 -/
def dropTrailingEmpty (s : List Layer) : List Layer :=
  (s.reverse.dropWhile Layer.isEmpty).reverse

private theorem length_dropWhile_le_bool {α : Type} (p : α → Bool) :
    ∀ xs : List α, (xs.dropWhile p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      by_cases h : p x = true
      · simp [List.dropWhile, h]
        exact Nat.le_trans (length_dropWhile_le_bool p xs) (Nat.le_succ xs.length)
      · simp [List.dropWhile, h]

/-- シェイプが正規化されている（末尾が空レイヤでない）ことを表す述語。
    0 層シェイプは正規化済みとみなす。 -/
def IsNormalized (s : Shape) : Prop :=
  s.getLast?.all (fun l => !l.isEmpty) = true

instance instDecidableIsNormalized : DecidablePred IsNormalized := fun _ =>
  inferInstanceAs (Decidable (_ = _))

/-- 末尾の空レイヤをストリップして正規化する。0 層なら 0 層を返す。 -/
def normalize (s : Shape) : Shape := dropTrailingEmpty s

/-- 正規化はレイヤ数を増やさない。 -/
theorem normalize.layerCount_le (s : Shape) :
    (normalize s).layerCount ≤ s.layerCount := by
  unfold normalize dropTrailingEmpty layerCount
  rw [List.length_reverse]
  exact Nat.le_trans (length_dropWhile_le_bool Layer.isEmpty s.reverse) (by simp)

end Shape

end S2IL
