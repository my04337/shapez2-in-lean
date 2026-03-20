-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.PartCode
import S2IL.Shape.Color

/-!
# Quarter (象限)

シェイプを4等分した各区画を表す型。
各象限は以下の3つの状態のいずれかをとる。

| コンストラクタ | シェイプコード | 説明 |
|---|---|---|
| `empty`              | `--`  | 空の象限（シェイプが存在しない） |
| `pin`                | `P-`  | ピン（色を持たない支持用パーツ） |
| `colored part color` | 例: `Cr`, `Rg` | 通常パーツコードとカラーコードの組 |

`colored` の `part` は `RegularPartCode` 型（ピンとクリスタルを除く4種）のみ受け付ける。
これにより `colored .pin _` や `colored .crystal _` を型レベルで禁止する。

- **ピン** はスタック時に隣接象限との落下判定が非接続になる特殊挙動を持つ
- **クリスタル** は脆弱 (Fragile) であり、落下・切断で破損するという特殊挙動を持つ
-/

/-- シェイプの象限を表す型。空 / ピン / 着色通常パーツ の3パターン -/
inductive Quarter where
    /-- 空の象限。シェイプコードでは `--` と表記する -/
    | empty
    /-- ピン。色を持たない支持用パーツ。シェイプコードでは `P-` と表記する -/
    | pin
    /-- 着色された通常パーツ。`part` は `RegularPartCode`（ピン・クリスタル除く） -/
    | colored (part : RegularPartCode) (color : Color)
    deriving Repr, DecidableEq, BEq

namespace Quarter

/-- 象限が空かどうかを判定する -/
def isEmpty : Quarter → Bool
    | empty => true
    | _     => false

/-- 象限のパーツコードを取得する。空の場合は `none` -/
def partCode? : Quarter → Option PartCode
    | empty         => none
    | pin           => some .pin
    | colored p _   => some p.toPartCode

/-- 象限の色を取得する。空・ピンの場合は `none` -/
def color? : Quarter → Option Color
    | colored _ c => some c
    | _           => none

/-- 象限を2文字のシェイプコード記法に変換する -/
def toNotation : Quarter → String
    | empty       => "--"
    | pin         => "P-"
    | colored p c => s!"{p.toChar}{c.toChar}"

/-- 2文字のシェイプコード記法から象限をパースする。無効な入力の場合は `none` -/
def fromNotation? (s : String) : Option Quarter :=
    match s.toList with
    | ['-', '-'] => some empty
    | ['P', '-'] => some pin
    | [c0, c1]   => match RegularPartCode.fromChar? c0, Color.fromChar? c1 with
        | some p, some c => some (colored p c)
        | _, _ => none
    | _ => none

/-- `fromNotation?` と `toNotation` のラウンドトリップ: 任意の `Quarter` に対して
    `fromNotation? (toNotation q) = some q` が成り立つ -/
theorem fromNotation_toNotation (q : Quarter) : fromNotation? (toNotation q) = some q := by
    cases q with
    | empty => rfl
    | pin => rfl
    | colored p c => cases p <;> cases c <;> rfl

end Quarter
