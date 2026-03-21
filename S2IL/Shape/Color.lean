-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Color (カラー)

象限の色情報を示すカラーコード。
シェイプコードにおいて各象限の色を1文字で表す。

| バリアント    | 記号 | 説明 |
|---|---|---|
| `red`       | `r` | レッド（原色） |
| `green`     | `g` | グリーン（原色） |
| `blue`      | `b` | ブルー（原色） |
| `yellow`    | `y` | イエロー（二次色: レッド + グリーン） |
| `cyan`      | `c` | シアン（二次色: グリーン + ブルー） |
| `magenta`   | `m` | マゼンタ（二次色: レッド + ブルー） |
| `white`     | `w` | ホワイト（三次色: 全混色） |
| `uncolored` | `u` | アンカラード（無着色） |

**注意**: `uncolored` は「色が塗られていない」という状態を表す色であり、
ピン (`P-`) や空の象限 (`--`) における色の不在 (`-`) とは異なる。
色の不在は `Quarter` 型の `empty` コンストラクタおよび `pin` コンストラクタで表現する。

なお `c` はカラーコード（シアン）とパーツコード（クリスタル）の両方で使用されるが、
型が異なるため Lean 上では曖昧さは生じない。
-/

/-- 象限の色情報を示すカラーコード -/
inductive Color where
    | red
    | green
    | blue
    | yellow
    | cyan
    | magenta
    | white
    | uncolored
    deriving Repr, DecidableEq, BEq

namespace Color

/-- カラーコードを対応するシェイプコード文字に変換する -/
def toChar : Color → Char
    | red       => 'r'
    | green     => 'g'
    | blue      => 'b'
    | yellow    => 'y'
    | cyan      => 'c'
    | magenta   => 'm'
    | white     => 'w'
    | uncolored => 'u'

/-- シェイプコード文字をカラーコードに変換する。無効な文字の場合は `none` を返す -/
def ofChar? : Char → Option Color
    | 'r' => some red
    | 'g' => some green
    | 'b' => some blue
    | 'y' => some yellow
    | 'c' => some cyan
    | 'm' => some magenta
    | 'w' => some white
    | 'u' => some uncolored
    | _   => none

/-- `ofChar?` と `toChar` のラウンドトリップ: 任意の `Color` に対して
    `ofChar? (toChar c) = some c` が成り立つ -/
theorem ofChar_toChar (c : Color) : ofChar? (toChar c) = some c := by
    cases c <;> rfl

/-- 全てのカラーコードのリスト -/
def all : List Color :=
    [red, green, blue, yellow, cyan, magenta, white, uncolored]

instance : ToString Color where
    toString c := c.toChar.toString

/-!
## 混色 (Color Mixing)

2つの色を等体積で混合した結果を返す。

### 混色モデル

各色を RGB 原色の重み付き成分で表し、等体積混合後に
各原色成分が閾値 (≥ 2/3) を超えるかで結果の色を判定する。

| 色 | R 成分 | G 成分 | B 成分 |
|---|---|---|---|
| Red       | 1   | 0   | 0   |
| Green     | 0   | 1   | 0   |
| Blue      | 0   | 0   | 1   |
| Yellow    | 1/2 | 1/2 | 0   |
| Cyan      | 0   | 1/2 | 1/2 |
| Magenta   | 1/2 | 0   | 1/2 |
| White     | 1/3 | 1/3 | 1/3 |
| Uncolored | 0   | 0   | 0   |

等体積混合: 各成分を平均し、≥ 1/3 なら原色ありと判定する。

**注意**: `uncolored` の液剤はゲーム上存在しないため、`uncolored` を含む
混色はゲーム上未定義である。ここでは数学的な拡張としてモデルに基づく値を定義する。
-/

/-- 2つの色を等体積で混合した結果を返す。
    ゲーム上の混色機 (Color Mixer) の動作に対応する。
    `uncolored` を含む混色はゲーム上未定義だが、数学的拡張として定義する。 -/
def mix : Color → Color → Color
    -- Red × 各色
    | red,       red       => red
    | red,       green     => yellow
    | red,       blue      => magenta
    | red,       yellow    => red
    | red,       cyan      => red
    | red,       magenta   => red
    | red,       white     => red
    | red,       uncolored => red
    -- Green × 各色
    | green,     red       => yellow
    | green,     green     => green
    | green,     blue      => cyan
    | green,     yellow    => green
    | green,     cyan      => green
    | green,     magenta   => green
    | green,     white     => green
    | green,     uncolored => green
    -- Blue × 各色
    | blue,      red       => magenta
    | blue,      green     => cyan
    | blue,      blue      => blue
    | blue,      yellow    => blue
    | blue,      cyan      => blue
    | blue,      magenta   => blue
    | blue,      white     => blue
    | blue,      uncolored => blue
    -- Yellow × 各色
    | yellow,    red       => red
    | yellow,    green     => green
    | yellow,    blue      => blue
    | yellow,    yellow    => yellow
    | yellow,    cyan      => green
    | yellow,    magenta   => red
    | yellow,    white     => yellow
    | yellow,    uncolored => uncolored
    -- Cyan × 各色
    | cyan,      red       => red
    | cyan,      green     => green
    | cyan,      blue      => blue
    | cyan,      yellow    => green
    | cyan,      cyan      => cyan
    | cyan,      magenta   => blue
    | cyan,      white     => cyan
    | cyan,      uncolored => uncolored
    -- Magenta × 各色
    | magenta,   red       => red
    | magenta,   green     => green
    | magenta,   blue      => blue
    | magenta,   yellow    => red
    | magenta,   cyan      => blue
    | magenta,   magenta   => magenta
    | magenta,   white     => magenta
    | magenta,   uncolored => uncolored
    -- White × 各色
    | white,     red       => red
    | white,     green     => green
    | white,     blue      => blue
    | white,     yellow    => yellow
    | white,     cyan      => cyan
    | white,     magenta   => magenta
    | white,     white     => white
    | white,     uncolored => uncolored
    -- Uncolored × 各色
    | uncolored, red       => red
    | uncolored, green     => green
    | uncolored, blue      => blue
    | uncolored, yellow    => uncolored
    | uncolored, cyan      => uncolored
    | uncolored, magenta   => uncolored
    | uncolored, white     => uncolored
    | uncolored, uncolored => uncolored

/-!
## 混色の代数的性質
-/

/-- 混色の可換性: `mix a b = mix b a` -/
theorem mix_comm (a b : Color) : mix a b = mix b a := by
    cases a <;> cases b <;> rfl

/-- 混色の冪等性: `mix a a = a` -/
theorem mix_self (a : Color) : mix a a = a := by
    cases a <;> rfl

/-- White は混色の左恒等元: `mix white a = a` -/
theorem mix_white_left (a : Color) : mix white a = a := by
    cases a <;> rfl

/-- White は混色の右恒等元: `mix a white = a` -/
theorem mix_white_right (a : Color) : mix a white = a := by
    cases a <;> rfl

/-- 混色は結合的でない: `mix (mix red green) blue ≠ mix red (mix green blue)` の反例 -/
theorem mix_not_assoc : mix (mix red green) blue ≠ mix red (mix green blue) := by
    decide

end Color
