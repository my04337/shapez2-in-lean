-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.PartCode
import S2IL.Shape.Color

/-!
# Quarter (象限)

シェイプを4等分した各区画を表す型。
各象限は以下の4つの状態のいずれかをとる。

| コンストラクタ | シェイプコード | 説明 |
|---|---|---|
| `empty`              | `--`  | 空の象限（シェイプが存在しない） |
| `pin`                | `P-`  | ピン（色を持たない支持用パーツ） |
| `crystal color`      | 例: `cr`, `cg` | クリスタル（脆弱な結晶パーツ、色を持つ） |
| `colored part color` | 例: `Cr`, `Rg` | 通常パーツコードとカラーコードの組 |

`colored` の `part` は `RegularPartCode` 型（ピンとクリスタルを除く4種）のみ受け付ける。
これにより `colored .pin _` や `colored .crystal _` を型レベルで禁止する。

- **ピン** はスタック時に隣接象限との落下判定が非接続になる特殊挙動を持つ
- **クリスタル** は脆弱 (Fragile) であり、落下・切断で破損するという特殊挙動を持つ
-/

/-- シェイプの象限を表す型。空 / ピン / クリスタル / 着色通常パーツ の4パターン -/
inductive Quarter where
    /-- 空の象限。シェイプコードでは `--` と表記する -/
    | empty
    /-- ピン。色を持たない支持用パーツ。シェイプコードでは `P-` と表記する -/
    | pin
    /-- クリスタル。脆弱な結晶パーツ。シェイプコードでは `c` + カラーコード（例: `cr`）と表記する -/
    | crystal (color : Color)
    /-- 着色された通常パーツ。`part` は `RegularPartCode`（ピン・クリスタル除く） -/
    | colored (part : RegularPartCode) (color : Color)
    deriving Repr, DecidableEq, BEq

namespace Quarter

/-- 象限が空かどうかを判定する -/
def isEmpty : Quarter → Bool
    | empty => true
    | _     => false

/-- 象限が構造結合を形成できるかを判定する。
    空とピン以外のシェイプ種別が結合能力を持つ -/
def canFormBond : Quarter → Bool
    | empty       => false
    | pin         => false
    | crystal _   => true
    | colored _ _ => true

/-- 象限が脆弱 (Fragile) かどうかを判定する。結晶のみが脆弱である -/
def isFragile : Quarter → Bool
    | crystal _ => true
    | _         => false

/-- 象限のパーツコードを取得する。空の場合は `none` -/
def partCode? : Quarter → Option PartCode
    | empty         => none
    | pin           => some .pin
    | crystal _     => some .crystal
    | colored p _   => some p.toPartCode

/-- 象限の色を取得する。空・ピンの場合は `none` -/
def color? : Quarter → Option Color
    | colored _ c => some c
    | crystal c   => some c
    | _           => none

/-- 象限を2文字のシェイプコード文字列に変換する -/
protected def toString : Quarter → String
    | empty       => "--"
    | pin         => "P-"
    | crystal c   => s!"c{c.toChar}"
    | colored p c => s!"{p.toChar}{c.toChar}"

instance : ToString Quarter where
    toString := Quarter.toString

/-- 2文字のシェイプコード文字列から象限をパースする。無効な入力の場合は `none` -/
def ofString? (s : String) : Option Quarter :=
    match s.toList with
    | ['-', '-'] => some empty
    | ['P', '-'] => some pin
    | ['c', c1]  => match Color.ofChar? c1 with
        | some c => some (crystal c)
        | none   => none
    | [c0, c1]   => match RegularPartCode.ofChar? c0, Color.ofChar? c1 with
        | some p, some c => some (colored p c)
        | _, _ => none
    | _ => none

/-- `ofString?` と `toString` のラウンドトリップ: 任意の `Quarter` に対して
    `ofString? (toString q) = some q` が成り立つ -/
theorem ofString_toString (q : Quarter) : ofString? q.toString = some q := by
    cases q with
    | empty => rfl
    | pin => rfl
    | crystal c => cases c <;> rfl
    | colored p c => cases p <;> cases c <;> rfl

end Quarter
