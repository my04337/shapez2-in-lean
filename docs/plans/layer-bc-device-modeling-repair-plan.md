# Layer B/C Device Modeling Repair Plan

> 作成日: 2026-05-16
> 最終更新: 2026-05-16

## Current Focus

- 対象: Layer B の装置セマンティクスと、Layer C の Flow primitive が参照する加工フロー
- 直近の目的: 実ゲームで確認できる加工装置レベルの入出力を先に確定し、Layer B 修正後に Layer C / 例題を最小手戻りで追従させる
- 次アクション: 下表のゲーム検証ケースを実機で確認し、観測結果を仕様仮説と照合する

## 目的

Layer C の加工フローは Layer B の公開装置 API を合成するため、Layer B 側の装置セマンティクスに漏れがあると、Flow 自体は型安全でもゲーム上は成立しないレシピを証明してしまう。

今回の修正では、構造操作と実ゲーム装置を明確に分ける。`eastHalf` / `westHalf` / `combineHalves` / `placeAbove` は数学的な構成部品として残しつつ、Cutter / Half-Destroyer / Swapper / Stacker / Pin Pusher などの装置 API は、ゲームで観測できる入出力に一致するように再点検する。

## 現在わかっている疑義

| 領域 | 疑義 | 現行 S2IL の状態 | 影響 |
|---|---|---|---|
| Cutter / Half-Destroyer | 切断時の crystal shatter が装置 API に統合されていない | `Shape.cut` / `Shape.halfDestroy` は raw `eastHalf` / `westHalf` | 結晶を含む切断レシピが過大に成立する |
| Cutter | 切断後の落下安定化が装置 API に統合されていない | 出力半分をそのまま返す | 西半分や上層片が浮いたまま出力されうる |
| Swapper | 各入力の `shatterOnCut` と切断後/合成後の扱いが未確定 | raw `eastHalf` / `westHalf` / `combineHalves` | 結晶をまたぐ入力で本来壊れる半分が残る |
| Stacker | 落下する crystal の shatter が落下処理へ統合されていない可能性 | `Shape.gravity` は移動のみで、`shatterOnFall` を呼ばない | 浮遊 crystal が落ちて残る可能性がある |
| Stacker / Pin Pusher | レイヤ上限超過時の shatter 判定順序が疑わしい | `truncate` 後に `shatterTopCrystals` | 廃棄レイヤに触れる crystal cluster を見逃す |
| Layer C | 構造 helper を実装例で物理装置のように扱える | `Flow.combineHalves` などは存在する | CrazyFinal などが structural recipe に寄りすぎる |

## ゲーム検証ケース

空出力は `""` と書く。ゲーム UI が空シェイプを出力しない場合は「無出力」として記録する。

Cutter の出力順はゲーム上の左右ポートではなく、形状で East half / West half として記録する。Swapper は S2IL 便宜上、`out1 = 入力Aの東 + 入力Bの西`, `out2 = 入力Bの東 + 入力Aの西` と呼ぶ。

| ID | 装置 / モード | 入力 | 仕様仮説の期待値 | 現行 S2IL の出力 | 確認したい点 |
|---|---|---|---|---|---|
| HD-1 | Half-Destroyer | `crcrcrcr` | `""` | `crcr----` | 東西をまたぐ crystal cluster が切断前に全砕けするか |
| CUT-1 | Cutter | `crcrcrcr` | East `""`, West `""` | East `crcr----`, West `----crcr` | Cutter でも同じく `shatterOnCut` が先に走るか |
| CUT-2 | Cutter | `cr--cr--` | East `cr------`, West `----cr--` | East `cr------`, West `----cr--` | 対角 crystal は結晶結合せず、不要に砕けないか |
| CUT-3 | Cutter | `CrCr----:--RgRg--` | East `CrCr----:--Rg----`, West `----Rg--` | East `CrCr----:--Rg----`, West `--------:----Rg--` | 切断後、浮いた西半分が下層へ落ちてから出力されるか |
| SWAP-1 | Swapper | A `crcrcrcr`, B `CuCuCuCu` | out1 `----CuCu`, out2 `CuCu----` | out1 `crcrCuCu`, out2 `CuCucrcr` | Swapper 入力ごとに切断 shatter が適用されるか |
| STACK-1 | Stacker / vanilla4 | bottom `--Cr----`, top `cr------` | `--Cr----` | `crCr----` | 浮遊 crystal が落下前に砕け、下の通常パーツだけ残るか |
| STACK-2 | Stacker / vanilla4 | bottom `Cr------`, top `cg------` | `Cr------:cg------` | `Cr------:cg------` | 支持された crystal は落下せず砕けないか |
| STACK-3 | Stacker / vanilla4 | bottom `CrCr----:cg------:cb------:cm------`, top `cw------` | `CrCr----` | `CrCr----:cg------:cb------:cm------` | 廃棄される 5 層目 crystal に結合する下位 cluster が砕けるか |
| PIN-1 | Pin Pusher / vanilla4 | `CrCr----:cg------:cb------:cm------` | `P-P-----:CrCr----` | `P-P-----:CrCr----:cg------:cb------` | 押し上げで廃棄される最上位 crystal から下位 cluster へ砕けが伝播するか |

`STACK-3` と `PIN-1` は、ゲーム UI が末尾空レイヤを保持して表示する場合、期待値がそれぞれ `CrCr----:--------:--------:--------` と `P-P-----:CrCr----:--------:--------` に見える可能性がある。正規化後は表の値と同じ扱いにする。

## 修正方針 / TODO

1. ゲーム検証結果をこの計画に反映する。
   - 仕様仮説と違うケースは、観測値を正として Layer B の処理順を更新する。
   - 出力ポート順や空出力の表記差は、Shape code と装置ポート名を分けて記録する。
2. Layer B に装置レベル API を再定義する。
   - `Shape.cut` / `Shape.halfDestroy` を raw half ではなく、Cutter / Half-Destroyer の完全セマンティクスに寄せるか、raw 操作を別名に分離する。
   - `settleAfterCut` 相当を導入し、切断後の各出力が settled になることをテストで固定する。
   - `Shape.swap` は入力ごとの切断 shatter と、ゲーム仕様上必要な後処理だけを統合する。
   - `Shape.stack` / `Shape.pinPush` は `truncate` 前の上限超過形状に対して crystal shatter を判定し、その後に切り詰める。
   - 落下 shatter が装置処理の一部なら、`Shape.gravity` とは別に device settling wrapper を用意する。
3. Layer B テストを装置単位で増やす。
   - 上記検証ケースを `Test/Operations` に追加する。
   - control case と failure case をペアにし、過剰 shatter と shatter 漏れを両方検出する。
4. Layer C を装置 API へ寄せる。
   - `Flow.cut` / `Flow.halfDestroy` / `Flow.swapShapes` / `Flow.stack` / `Flow.pinPush` は修正後 Layer B API を参照する。
   - `Flow.combineHalves` や `Shape.placeAbove` 系は structural helper と明記し、ゲーム装置レシピの正当性主張には使わない。
   - `Test/Flow/CrazyFinal.lean` は修正完了まで structural sketch として扱い、物理的妥当性の exact test にしない。
5. ドキュメントを同期する。
   - `docs/shapez2/game-system-overview.md` の装置説明と Layer B 実装の処理順を一致させる。
   - `docs/plans/layer-c-flow-design-implementation-plan.md` の primitive 表に、device API と structural helper の区別を追記する。
   - `docs/plans/MILESTONES.md` の B-4 / C-1 / Non-Wire Solver の状態を更新する。

## 受け入れ基準

- ゲーム検証ケースの観測値が、Layer B の device-level tests として Lean 側に固定されている。
- Cutter / Half-Destroyer / Swapper / Stacker / Pin Pusher の公開 Flow primitive が、raw structural helper ではなく装置セマンティクスを評価する。
- Layer C の代表例は、structural sketch と physical device flow のどちらかを明示している。
- `Test` target が通り、既存の Layer A/B の定理名と import 構造を不要に崩していない。

## CrazyFinal の扱い

`CrazyFinal` は、現時点では complex target を構造的に組み立てるスケッチとして価値がある一方で、Cutter / Stacker / Pin Pusher の疑義が解消するまでは「ゲーム内でそのまま実現できる加工フロー」として扱わない。

Layer B 修正後に、次のどちらかへ整理する。

- physical route: 実装済み装置 API だけで target `RmCcWcCm:--cm--cc:RcccCmcm:cmcccccm:cw--cw--` へ到達する Flow として再構成する。
- structural benchmark: reverse solver の探索目標や組立補助として残し、装置妥当性テストからは外す。
