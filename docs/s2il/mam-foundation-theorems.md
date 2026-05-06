# MAM 前提 theorem inventory

> 作成日: 2026-05-06
> 最終更新: 2026-05-06

完了済みの Layer B MAM 前提証明計画から残す、MAM 前提 theorem の索引。
ここには作業計画ではなく、実装済み API、検証済みの方角仕様、今後強化するときの注意点だけを置く。

## 1. 完了した範囲

| 範囲 | 完了内容 | 正本 |
|---|---|---|
| 象限抽出フロー例 | `halfDestroy -> rotate* -> halfDestroy` の固定加工ライン例を theorem 化 | `S2IL/Flow/QuadrantExtraction.lean` |
| Stacker correctness | 出力安定性、レイヤ数上界、単一象限入力 invariants を theorem 化 | `S2IL/Operations/Stacker.lean` |
| 等変性棚卸し | E/W 参照操作の例外と Stacker 合成チェーンを整理 | `docs/s2il/architecture-layer-ab.md` |
| MAM 文書 | T-1〜T-12 の状態を現行 Lean 実装へ同期 | `docs/shapez2/mam.md` |

## 2. 象限抽出フロー例

ゲーム上の MAM で中心となる図形解析は Wire 系の図形分析器 (Shape Analyzer) である。
`halfDestroy -> rotate* -> halfDestroy` は Operation API ではなく、Layer C-1 Flow の固定加工ラインサンプルとして扱う。

現行の方角定義:

| 値 | 方角 |
|---|---|
| `0` | NE |
| `1` | SE |
| `2` | SW |
| `3` | NW |

代表入力 `CrRgSbWy` で確定した挙動:

| 工程 | 出力 | 意味 |
|---|---|---|
| `halfDestroy` | `CrRg----` | 東半分、つまり NE/SE を残す |
| `halfDestroy -> rotateCW -> halfDestroy` | `--Cr----` | 元 NE を SE に残す |
| `halfDestroy -> rotateCCW -> halfDestroy` | `Rg------` | 元 SE を NE に残す |
| `halfDestroy -> rotate180 -> halfDestroy` | `--------` | 最初の東半分が西側へ移るため空になる |

公開 theorem:

| theorem | 役割 |
|---|---|
| `Flow.QuadrantExtraction.halfDestroy_getQuarter` | `halfDestroy` の点ごとの仕様 |
| `Flow.QuadrantExtraction.rotateCW_getDir` | CW 回転後に参照する元 direction |
| `Flow.QuadrantExtraction.rotateCCW_getDir` | CCW 回転後に参照する元 direction |
| `Flow.QuadrantExtraction.rotate180_getDir` | 180° 回転後に参照する元 direction |
| `Flow.QuadrantExtraction.extractAfterRotateCW_getQuarter` | 2 段切断 + CW の点ごとの仕様 |
| `Flow.QuadrantExtraction.extractAfterRotateCCW_getQuarter` | 2 段切断 + CCW の点ごとの仕様 |
| `Flow.QuadrantExtraction.extractAfterRotate180_getQuarter` | 2 段切断 + 180° の点ごとの仕様 |
| `Flow.QuadrantExtraction.complete` | 全象限を NE 位置へ抽出できること |

代表値と型確認は `Test/Flow/QuadrantExtraction.lean` に置く。

## 3. Stacker correctness

公開 theorem:

| theorem | 役割 |
|---|---|
| `Shape.stack.isSettled` | `Shape.stack bottom top config` は常に `IsSettled` |
| `Shape.stack.layerCount_le` | `stack` の出力レイヤ数は `config.maxLayers` 以下 |
| `Shape.IsSingleQuadrantShape` | 1 レイヤで指定方角以外が空の shape predicate |
| `Shape.stack.singleQuadrant_invariants` | 単一象限入力に対して `IsSettled` とレイヤ数上界を同時に得る |

レイヤ数上界の補助 theorem:

| theorem | 役割 |
|---|---|
| `Shape.normalize.layerCount_le` | 正規化はレイヤ数を増やさない |
| `Shape.shatterMask.layerCount` | shatter mask はレイヤ数を変えない |
| `Shape.shatterTopCrystals.layerCount_le` | 切り詰め時砕け散りはレイヤ数を増やさない |
| `Shape.waveStep.layerCount` | wave step はレイヤ数を変えない |
| `Shape.waveGravityCoreFast.layerCount` | fast gravity core はレイヤ数を変えない |
| `Shape.gravity.layerCount_le` | gravity は正規化込みでレイヤ数を増やさない |

`Shape.stack.singleQuadrant_invariants` は保守的な invariants theorem であり、出力の正確な位置挙動までは主張しない。
位置挙動を強化する場合は、少なくとも次を分離してから theorem 化する。

| 条件 | 理由 |
|---|---|
| crystal を含むか | `shatterTopCrystals` がクラスタを消す可能性がある |
| pin を含むか | 浮遊・支えの意味論が通常パーツと異なる可能性がある |
| `config.maxLayers` が十分か | `truncate` で上側が消える可能性がある |
| 中間形状が settled / normalized か | `Shape.gravity.of_isSettled` には正規化前提が必要 |

## 4. 参照先

| 目的 | 参照先 |
|---|---|
| MAM 仕様上の theorem 状態 | `docs/shapez2/mam.md` |
| Layer A/B の API 境界と例外規則 | `docs/s2il/architecture-layer-ab.md` |
| Flow 側の代表固定フロー計画 | `docs/plans/layer-c1-shape-processing-flow-plan.md` |
| 現在の sorry 状態 | `S2IL/_agent/sorry-goals.md` |