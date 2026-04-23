# 全加工装置の gravity 利用・IsSettled 必要性マトリクス

> 作成日: 2026-04-09

---

## gravity 利用状況

| 加工装置 | 関数 | gravity 呼び出し | gravity 入力の layerCount |
|---|---|---|---|
| 着色機 (Painter) | `Shape.paint` | なし | — |
| 結晶製造機 (CrystalGenerator) | `Shape.crystallize` | なし | — |
| 回転機 (Rotator) | `Shape.rotateCW/CCW/180` | なし | — |
| 混色機 (ColorMixer) | `ColorMixer.mix` | なし（色操作のみ） | — |
| **ピン押し機 (PinPusher)** | `Shape.pinPush` | `truncated.gravity` | ≤ maxLayers |
| **積層機 (Stacker)** | `Shape.stack` | ① `afterShatter.gravity` | ≤ 2×maxLayers |
| | | ② `truncated.gravity` | ≤ maxLayers |
| **切断機 (Cutter)** | `Shape.cut` | `settleAfterCut` × 2 | ≤ 入力 layerCount |
| **切断処理機 (HalfDestroy)** | `Shape.halfDestroy` | `settleAfterCut` × 1 | ≤ 入力 layerCount |
| **スワップ機 (Swapper)** | `Shape.swap` | `settleAfterCut` × 2 | ≤ 各入力 layerCount |

## rotate180 等変性定理の現状

| 加工装置 | 定理 | 仮説 | sorry |
|---|---|---|---|
| Painter | `paint_rotate180_comm` | なし | なし |
| CrystalGenerator | `crystallize_rotate180_comm` | なし | なし |
| Rotator | `rotateCW_rotate180_comm` 等 | なし | なし |
| PinPusher | `pinPush_rotate180_comm` | `config.maxLayers ≤ 5` | なし |
| Stacker | `stack_rotate180_comm` | `config.maxLayers ≤ 5` + `IsSettled` | なし（axiom 依存） |
| Cutter | `cut_rotate180_comm` | `s.layerCount ≤ 5` | なし |
| HalfDestroy | `halfDestroy_rotate180` | `s.layerCount ≤ 5` | なし |
| Swapper | `swap_rotate180_comm` | `s1.layerCount ≤ 5 ∧ s2.layerCount ≤ 5` + 両入力の settleAfterCut が some | なし |

## IsSettled 導入の必要性（vanilla4/5 の範囲）

### IsSettled 導入が必要な加工工程

| 加工装置 | 対象 gravity 呼び出し | 理由 |
|---|---|---|
| **Stacker (1st gravity)** | `shatterTopCrystals(placeAbove b t).gravity` | placeAbove 出力が 2×maxLayers まで膨張。`layerCount ≤ 5` を満たせない |

### IsSettled 導入が不要な加工工程

| 加工装置 | 理由 |
|---|---|
| Painter, CrystalGenerator, Rotator, ColorMixer | gravity を呼ばない |
| PinPusher | gravity 入力 ≤ maxLayers ≤ 5 |
| Stacker (2nd gravity) | gravity 入力 ≤ maxLayers ≤ 5（truncate 後） |
| Cutter, HalfDestroy, Swap | gravity 入力 ≤ 入力 layerCount ≤ maxLayers ≤ 5 |

## 備考

- `process_rotate180` は **旧 foldl モデルで** ≥6L のシェイプに対して偽（反例あり）。Wave Gravity モデルへの移行後はこの制限は無関係
- 上表の `≤ 5` 仮説はすべて旧 foldl（1 パス）実装に由来する制約。Wave Gravity モデルでは不要となる
- game-settled 保証: ゲーム上、全加工装置の入力は他の Machine 出力（gravity 経由）→ 常に settled
- Swapper の `combineHalves` 後は `normalize` のみ（gravity なし）。浮遊ユニット発生の可能性は別途確認が必要
