-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Kernel
import S2IL.Operations.Common
import S2IL.Operations.Shatter.Internal.Mask

/-!
# S2IL.Operations.Shatter.Defs

砕け散り操作の定義層。
-/

namespace S2IL

/-- 位置述語 `P` が真な象限を `Quarter.empty` に置換する。
    各 shatter 操作（`shatterOnFall` / `shatterOnCut` / `shatterTopCrystals`）は
    本 primitive を異なる `P` で具体化したものとして定義される。 -/
def Shape.shatterMask (s : Shape) (P : QuarterPos → Bool) : Shape :=
  Shatter.Internal.shatterMaskFrom (fun n d => P (n, d)) 0 s

/-- 落下時砕け散り判定: 位置 `p` は、`ps` 中の脆弱な象限と結晶結合クラスタで連結している。 -/
def IsShatteredOnFall (s : Shape) (ps : List QuarterPos) (p : QuarterPos) : Prop :=
  ∃ t ∈ ps, (QuarterPos.getQuarter s t).isFragile = true ∧ CrystalBondClusterRel s t p

noncomputable instance (s : Shape) (ps : List QuarterPos) :
    DecidablePred (IsShatteredOnFall s ps) := Classical.decPred _

/-- 落下時砕け散り。`ps` は落下対象象限の位置リスト。脆弱な象限を含む結晶結合クラスタ全体を
    `Quarter.empty` に置換する（[docs/shapez2/crystal-shatter.md §4.1](../../docs/shapez2/crystal-shatter.md)）。 -/
noncomputable def Shape.shatterOnFall (s : Shape) (ps : List QuarterPos) : Shape :=
  s.shatterMask (fun p => decide (IsShatteredOnFall s ps p))

/-- 切り詰め時砕け散り判定: 位置 `p` は、層番号 `≥ threshold` にある結晶象限と
  結晶結合クラスタで連結している。 -/
def IsShatteredOnTruncate (s : Shape) (threshold : Nat) (p : QuarterPos) : Prop :=
  ∃ t : QuarterPos, threshold ≤ t.1 ∧ (QuarterPos.getQuarter s t).isCrystal = true
                    ∧ CrystalBondClusterRel s t p

noncomputable instance (s : Shape) (threshold : Nat) :
    DecidablePred (IsShatteredOnTruncate s threshold) := Classical.decPred _

/-- 切り詰め時砕け散り。`threshold` レイヤ以上に存在する結晶を含む結晶結合クラスタを全て消去する
    （[docs/shapez2/crystal-shatter.md §4.3](../../docs/shapez2/crystal-shatter.md)）。
    Stacker / PinPusher のレイヤ上限切り詰め時に用いる。 -/
noncomputable def Shape.shatterTopCrystals (s : Shape) (threshold : Nat) : Shape :=
  s.shatterMask (fun p => decide (IsShatteredOnTruncate s threshold p))

/-- 切断時砕け散り判定: 位置 `p` は、東半分と西半分の両方の結晶象限を含む
  結晶結合クラスタの構成員である。 -/
def IsShatteredOnCut (s : Shape) (p : QuarterPos) : Prop :=
  ∃ t : QuarterPos, (QuarterPos.getQuarter s t).isCrystal = true
                    ∧ CrystalBondClusterRel s t p
                    ∧ (∃ pE, CrystalBondClusterRel s t pE ∧ Direction.isEast pE.2 = true)
                    ∧ (∃ pW, CrystalBondClusterRel s t pW ∧ Direction.isWest pW.2 = true)

noncomputable instance (s : Shape) :
    DecidablePred (IsShatteredOnCut s) := Classical.decPred _

/-- 切断時砕け散り。東西跨ぎ結晶結合クラスタの結晶を全て消去する
    （[docs/shapez2/crystal-shatter.md §4.2](../../docs/shapez2/crystal-shatter.md)）。
    `cut` / `halfDestroy` / `swap` の前段で適用される。 -/
noncomputable def Shape.shatterOnCut (s : Shape) : Shape :=
  s.shatterMask (fun p => decide (IsShatteredOnCut s p))

end S2IL