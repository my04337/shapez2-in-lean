-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Quarter

/-!
# Layer (レイヤ)

シェイプを垂直方向に積み重ねる単位となる、4象限の組を表す型。

各象限は方角で識別され、シェイプコードでは右上 (`ne`) を起点に
時計回り (`ne` → `se` → `sw` → `nw`) の順で記述する。

| フィールド | 方角 | 位置 |
|---|---|---|
| `ne` | Northeast | 右上 |
| `se` | Southeast | 右下 |
| `sw` | Southwest | 左下 |
| `nw` | Northwest | 左上 |

#### 西側・東側の半分

切断系操作で参照される半分は以下のように対応する。

| 半分 | 含まれる象限 |
|---|---|
| West Half (西側の半分) | `nw`, `sw` |
| East Half (東側の半分) | `ne`, `se` |
-/

/-- シェイプの1レイヤを表す4象限の組 -/
structure Layer where
    /-- 右上 (Northeast) の象限 -/
    ne : Quarter
    /-- 右下 (Southeast) の象限 -/
    se : Quarter
    /-- 左下 (Southwest) の象限 -/
    sw : Quarter
    /-- 左上 (Northwest) の象限 -/
    nw : Quarter
    deriving Repr, DecidableEq, BEq

namespace Layer

/-- レイヤの全象限が空かどうかを判定する -/
def isEmpty (l : Layer) : Bool :=
    l.ne.isEmpty && l.se.isEmpty && l.sw.isEmpty && l.nw.isEmpty

/-- レイヤをシェイプコード記法に変換する（右上起点で時計回り） -/
def toNotation (l : Layer) : String :=
    l.ne.toNotation ++ l.se.toNotation ++ l.sw.toNotation ++ l.nw.toNotation

/-- 8文字のシェイプコード記法からレイヤをパースする。無効な入力の場合は `none` -/
def fromNotation? (s : String) : Option Layer :=
    match s.toList with
    | [a, b, c, d, e, f, g, h] =>
        match Quarter.fromNotation? (String.ofList [a, b]),
              Quarter.fromNotation? (String.ofList [c, d]),
              Quarter.fromNotation? (String.ofList [e, f]),
              Quarter.fromNotation? (String.ofList [g, h]) with
        | some ne, some se, some sw, some nw => some { ne, se, sw, nw }
        | _, _, _, _ => none
    | _ => none

/-- `toNotation` の各象限部分を `String.ofList` で再構築すると元の `toNotation` に戻る -/
private theorem ofList_quarter_toList (q : Quarter) :
        String.ofList q.toNotation.toList = q.toNotation :=
    String.ofList_toList

/-- `fromNotation?` と `toNotation` のラウンドトリップ: 任意の `Layer` に対して
    `fromNotation? (toNotation l) = some l` が成り立つ -/
theorem fromNotation_toNotation (l : Layer) : fromNotation? (toNotation l) = some l := by
    simp only [fromNotation?, toNotation, String.toList_append]
    suffices h : ∀ (q : Quarter),
            ∃ a b, q.toNotation.toList = [a, b] ∧
                   Quarter.fromNotation? (String.ofList [a, b]) = some q by
        obtain ⟨a, b, hab, hne⟩ := h l.ne
        obtain ⟨c, d, hcd, hse⟩ := h l.se
        obtain ⟨e, f, hef, hsw⟩ := h l.sw
        obtain ⟨g, hh, hgh, hnw⟩ := h l.nw
        rw [hab, hcd, hef, hgh]
        simp only [List.cons_append, List.nil_append, hne, hse, hsw, hnw]
    intro q
    cases q with
    | empty => exact ⟨'-', '-', rfl, rfl⟩
    | pin   => exact ⟨'P', '-', rfl, rfl⟩
    | colored p c =>
        -- toNotation は "XY" 形式（Xがパーツ文字、Yがカラー文字）
        -- cases で全通り展開して具体値を直接与える
        cases p <;> cases c <;> exact ⟨_, _, rfl, rfl⟩

end Layer
