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
| `pin`       | `P` | ピン（支持用、特殊扱い） |
| `crystal`   | `c` | クリスタル（結晶形、脆弱・特殊扱い） |

空の象限は `PartCode` に含めない。
空の象限はタスク 1-1-3 で `Quarter` 型として `Option` で表現する。

ピン (`pin`) とクリスタル (`crystal`) はゲーム上の特殊な挙動を持つため、
通常シェイプのみを表す `RegularPartCode` を別途定義する。
-/

/-- 象限のシェイプ種別を示すパーツコード（全6種） -/
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

instance : ToString PartCode where
    toString p := p.toChar.toString

end PartCode

/-!
# Regular Part Code (通常パーツコード)

ピン (`pin`) とクリスタル (`crystal`) を除いた通常シェイプのパーツコード。

- **ピン** はゲーム上で特殊な接続挙動（隣接象限との落下判定非接続）を持つ
- **クリスタル** は脆弱 (Fragile) であり、落下・切断で破損するという特殊な挙動を持つ

`Quarter.colored` の `part` フィールドはこの型を使用することで、
型レベルでピンと結晶を着色象限に含めることを禁止する。

| バリアント | 記号 | 説明 |
|---|---|---|
| `circle`    | `C` | サークル（円形） |
| `rectangle` | `R` | レクタングル（四角形） |
| `star`      | `S` | スター（星形） |
| `windmill`  | `W` | ウィンドミル（風車形） |
-/

/-- ピンとクリスタルを除いた通常シェイプのパーツコード -/
inductive RegularPartCode where
    | circle
    | rectangle
    | star
    | windmill
    deriving Repr, DecidableEq, BEq

namespace RegularPartCode

/-- 通常パーツコードを対応するシェイプコード文字に変換する -/
def toChar : RegularPartCode → Char
    | circle    => 'C'
    | rectangle => 'R'
    | star      => 'S'
    | windmill  => 'W'

/-- シェイプコード文字を通常パーツコードに変換する。無効な文字の場合は `none` を返す -/
def fromChar? : Char → Option RegularPartCode
    | 'C' => some circle
    | 'R' => some rectangle
    | 'S' => some star
    | 'W' => some windmill
    | _   => none

/-- `fromChar?` と `toChar` のラウンドトリップ: 任意の `RegularPartCode` に対して
    `fromChar? (toChar p) = some p` が成り立つ -/
theorem fromChar_toChar (p : RegularPartCode) : fromChar? (toChar p) = some p := by
    cases p <;> rfl

/-- 通常パーツコードを `PartCode` に変換する -/
def toPartCode : RegularPartCode → PartCode
    | circle    => .circle
    | rectangle => .rectangle
    | star      => .star
    | windmill  => .windmill

/-- `PartCode` から通常パーツコードに変換する。ピン・クリスタルの場合は `none` を返す -/
def ofPartCode? : PartCode → Option RegularPartCode
    | .circle    => some circle
    | .rectangle => some rectangle
    | .star      => some star
    | .windmill  => some windmill
    | .pin       => none
    | .crystal   => none

/-- `ofPartCode? (toPartCode p) = some p` が成り立つ -/
theorem ofPartCode_toPartCode (p : RegularPartCode) : ofPartCode? (toPartCode p) = some p := by
    cases p <;> rfl

/-- 全ての通常パーツコードのリスト -/
def all : List RegularPartCode :=
    [circle, rectangle, star, windmill]

instance : ToString RegularPartCode where
    toString p := p.toChar.toString

end RegularPartCode
