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

各色を RGB 原色のビット表現で表す。

| 色 | R | G | B |
|---|---|---|---|
| Red       | 1 | 0 | 0 |
| Green     | 0 | 1 | 0 |
| Blue      | 0 | 0 | 1 |
| Yellow    | 1 | 1 | 0 |
| Cyan      | 0 | 1 | 1 |
| Magenta   | 1 | 0 | 1 |
| White     | 1 | 1 | 1 |
| Uncolored | 0 | 0 | 0 |

**混色規則**: `mix(a, b) = if (a AND b ≠ 0) then (a AND b) else (a OR b)`

つまり共通の原色成分があれば交集合、なければ和集合を取る。

- `Uncolored` は恒等元（`mix uncolored x = x`）
- `White` は `Uncolored` 以外に対して恒等的（`mix white x = x` for `x ≠ uncolored`）
- 補色ペア（共通成分なし）の混色は `White`
  （例: `red + cyan = white`, `green + magenta = white`）
-/

/-- 2つの色を等体積で混合した結果を返す。
    ゲーム上の混色機 (Color Mixer) の動作に対応する。
    混色規則: 共通原色成分があれば交集合、なければ和集合。 -/
def mix : Color → Color → Color
    -- Red × 各色
    | red,       red       => red
    | red,       green     => yellow
    | red,       blue      => magenta
    | red,       yellow    => red
    | red,       cyan      => white
    | red,       magenta   => red
    | red,       white     => red
    | red,       uncolored => red
    -- Green × 各色
    | green,     red       => yellow
    | green,     green     => green
    | green,     blue      => cyan
    | green,     yellow    => green
    | green,     cyan      => green
    | green,     magenta   => white
    | green,     white     => green
    | green,     uncolored => green
    -- Blue × 各色
    | blue,      red       => magenta
    | blue,      green     => cyan
    | blue,      blue      => blue
    | blue,      yellow    => white
    | blue,      cyan      => blue
    | blue,      magenta   => blue
    | blue,      white     => blue
    | blue,      uncolored => blue
    -- Yellow × 各色
    | yellow,    red       => red
    | yellow,    green     => green
    | yellow,    blue      => white
    | yellow,    yellow    => yellow
    | yellow,    cyan      => green
    | yellow,    magenta   => red
    | yellow,    white     => yellow
    | yellow,    uncolored => yellow
    -- Cyan × 各色
    | cyan,      red       => white
    | cyan,      green     => green
    | cyan,      blue      => blue
    | cyan,      yellow    => green
    | cyan,      cyan      => cyan
    | cyan,      magenta   => blue
    | cyan,      white     => cyan
    | cyan,      uncolored => cyan
    -- Magenta × 各色
    | magenta,   red       => red
    | magenta,   green     => white
    | magenta,   blue      => blue
    | magenta,   yellow    => red
    | magenta,   cyan      => blue
    | magenta,   magenta   => magenta
    | magenta,   white     => magenta
    | magenta,   uncolored => magenta
    -- White × 各色
    | white,     red       => red
    | white,     green     => green
    | white,     blue      => blue
    | white,     yellow    => yellow
    | white,     cyan      => cyan
    | white,     magenta   => magenta
    | white,     white     => white
    | white,     uncolored => white
    -- Uncolored × 各色
    | uncolored, red       => red
    | uncolored, green     => green
    | uncolored, blue      => blue
    | uncolored, yellow    => yellow
    | uncolored, cyan      => cyan
    | uncolored, magenta   => magenta
    | uncolored, white     => white
    | uncolored, uncolored => uncolored

/-!
## 混色の代数的性質
-/

/-- 混色の可換性: `mix a b = mix b a` -/
theorem mix_comm (a b : Color) : mix a b = mix b a := by
    cases a <;> cases b <;> rfl

/-- 混色の冪等性: `mix a a = a` -/
@[simp] theorem mix_self (a : Color) : mix a a = a := by
    cases a <;> rfl

/-- Uncolored は混色の左恒等元: `mix uncolored a = a` -/
@[simp] theorem mix_uncolored_left (a : Color) : mix uncolored a = a := by
    cases a <;> rfl

/-- Uncolored は混色の右恒等元: `mix a uncolored = a` -/
@[simp] theorem mix_uncolored_right (a : Color) : mix a uncolored = a := by
    cases a <;> rfl

/-!
## 型クラスインスタンス

混色の代数的性質を `Std` の型クラスとして登録する。
これにより `Std.Commutative.comm`、`Std.IdempotentOp.idempotent`、
`Std.LawfulLeftIdentity.left_id` 等が型クラス推論で自動的に利用可能になる。
-/

instance : Std.Commutative Color.mix where
    comm := mix_comm

instance : Std.IdempotentOp Color.mix where
    idempotent := mix_self

instance : Std.LeftIdentity Color.mix Color.uncolored := ⟨⟩
instance : Std.LawfulLeftIdentity Color.mix Color.uncolored where
    left_id := mix_uncolored_left

instance : Std.RightIdentity Color.mix Color.uncolored := ⟨⟩
instance : Std.LawfulRightIdentity Color.mix Color.uncolored where
    right_id := mix_uncolored_right

/-- 混色は結合的でない: `mix (mix red yellow) cyan ≠ mix red (mix yellow cyan)` の反例 -/
theorem mix_not_assoc : mix (mix red yellow) cyan ≠ mix red (mix yellow cyan) := by
    decide

end Color
