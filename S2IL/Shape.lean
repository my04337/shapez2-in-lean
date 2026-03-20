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
例: `CuCuCuCu:RrRrRrRr` は下層がサークル(無着色)、上層がレクタングル(赤) の 2 レイヤシェイプ。

> **注記**: 現時点では、空中に浮いたレイヤ等、ゲームシステム上の物理的制約には
> 対応していない。これらは Stacking・Cutting などの操作関数を定義する際に考慮する。
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

/-- `layers` の長さは `layerCount` と等しい -/
theorem layers_length (s : Shape) : s.layers.length = s.layerCount := by
    cases s <;> rfl

/-- `layers` は空でない -/
theorem layers_nonempty (s : Shape) : s.layers ≠ [] := by
    cases s <;> simp [layers]

/-- シェイプをシェイプコード記法に変換する（レイヤを `:` 区切りで下層から上層の順に連結） -/
def toNotation (s : Shape) : String :=
    ":".intercalate (s.layers.map Layer.toNotation)

end Shape
