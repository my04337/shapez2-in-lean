-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

/-!
# Part Code (パーツコード)

象限のシェイプ種別を示すコード。
シェイプコードにおいて各象限の形状を1文字で表す。

| バリアント | 記号 | 説明 |
|---|---|---|
| `circle`    | `C` | サークル（円形） |
| `rectangle` | `R` | レクタングル（四角形） |
| `star`      | `S` | スター（星形） |
| `windmill`  | `W` | ウィンドミル（風車形） |
| `pin`       | `P` | ピン（支持用） |
| `crystal`   | `c` | クリスタル（結晶形、脆弱） |

空の象限は `PartCode` に含めない。
空の象限はタスク 1-1-3 で `Quarter` 型として `Option` で表現する。
-/

/-- 象限のシェイプ種別を示すパーツコード -/
inductive PartCode where
    | circle
    | rectangle
    | star
    | windmill
    | pin
    | crystal
    deriving Repr, DecidableEq, BEq

namespace PartCode

/-- パーツコードを対応するシェイプコード文字に変換する -/
def toChar : PartCode → Char
    | circle    => 'C'
    | rectangle => 'R'
    | star      => 'S'
    | windmill  => 'W'
    | pin       => 'P'
    | crystal   => 'c'

/-- シェイプコード文字をパーツコードに変換する。無効な文字の場合は `none` を返す -/
def fromChar? : Char → Option PartCode
    | 'C' => some circle
    | 'R' => some rectangle
    | 'S' => some star
    | 'W' => some windmill
    | 'P' => some pin
    | 'c' => some crystal
    | _   => none

/-- `fromChar?` と `toChar` のラウンドトリップ: 任意の `PartCode` に対して
    `fromChar? (toChar p) = some p` が成り立つ -/
theorem fromChar_toChar (p : PartCode) : fromChar? (toChar p) = some p := by
    cases p <;> rfl

/-- 全てのパーツコードのリスト -/
def all : List PartCode :=
    [circle, rectangle, star, windmill, pin, crystal]

end PartCode
