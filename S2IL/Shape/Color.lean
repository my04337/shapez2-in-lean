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
| `yellow`    | `y` | イエロー（二次色: Red + Green） |
| `cyan`      | `c` | サイアン（二次色: Green + Blue） |
| `magenta`   | `m` | マゼンタ（二次色: Red + Blue） |
| `white`     | `w` | ホワイト（三次色: 全混色） |
| `uncolored` | `u` | アンカラード（無着色） |

**注意**: `uncolored` は「色が塗られていない」という状態を表す色であり、
ピン (`P-`) や空の象限 (`--`) における色の不在 (`-`) とは異なる。
色の不在はタスク 1-1-3 で `Quarter` 型として表現する。

なお `c` はカラーコード（サイアン）とパーツコード（クリスタル）の両方で使用されるが、
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
def fromChar? : Char → Option Color
    | 'r' => some red
    | 'g' => some green
    | 'b' => some blue
    | 'y' => some yellow
    | 'c' => some cyan
    | 'm' => some magenta
    | 'w' => some white
    | 'u' => some uncolored
    | _   => none

/-- `fromChar?` と `toChar` のラウンドトリップ: 任意の `Color` に対して
    `fromChar? (toChar c) = some c` が成り立つ -/
theorem fromChar_toChar (c : Color) : fromChar? (toChar c) = some c := by
    cases c <;> rfl

/-- 全てのカラーコードのリスト -/
def all : List Color :=
    [red, green, blue, yellow, cyan, magenta, white, uncolored]

instance : ToString Color where
    toString c := c.toChar.toString

end Color
