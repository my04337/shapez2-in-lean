# Gravity 証明 — 実行計画

> 作成日: 2026-04-05
> 最終更新: 2026-04-15 (計画簡素化, セクション番号再編, Wave Gravity 記述復元)

---

## 現状クイックリファレンス

| 指標 | 値 |
|---|---|
| ビルド状態 | errors=0, warnings=0 |
| sorry | **0 件** |
| axiom | **5 件**（§2 参照）|
| 裸 simp | **0 個**（T-2 完了: SettledState 72箇所 + CommExt 4箇所 → 全て `simp only` / `simp_all only` 化） |
| r180 等変性 | 全操作で完了 |
| rCW 等変性 | 全操作で完了（Phase F LayerPerm 統合完了。R-1 完了） |

---

## 残作業 TODO

| # | タスク | 対応セクション | 概要 | 推定工数 |
|---|---|---|---|---|
| T-5 | Wave Gravity Model | §3 | axiom 5件の除去・新モデル実装 | 3-5 s |

**推奨実施順序**: T-5

---

## §1 全体タスク依存グラフ

```
T-5: Wave Gravity Model (axiom 除去・新モデル実装)
```

---

## §2 Axiom インベントリ

5件の axiom が残存。すべて **Wave Gravity Model（§3）** の導入で構成的証明に置換可能。

| axiom 名 | ファイル | 型シグネチャ（概要） | 計算検証 |
|---|---|---|---|
| `gravity_IsSettled` | SettledState.lean | `∀ (s : Shape), h_lc : s.layerCount ≤ 5 → IsSettled (Gravity.process s)` | 1.9M+ shapes (≤5L) 0 failures |
| `all_grounded_settle_foldl` | SettledState.lean | foldl 帰納ステップの AllNonEmptyGrounded 保存（private） | 5L 2dir 全数 0 failures |
| `process_rotate180_placeAbove_settled` | Stacker.lean | settled 入力の placeAbove + shatter 後 gravity が r180 等変 | 166,757+ settled shapes 0 failures |
| `process_rotateCW_placeAbove_settled` | Stacker.lean | settled 入力の placeAbove + shatter 後 gravity が rCW 等変 | r180 版と同一検証基盤 |
| `IsSettled_liftUp_generatePins` | PinPusher.lean | settled 入力の liftUp+generatePins は settled（private） | SettledShape 追加時に検証済み |

### 除去ロードマップ（§3 Wave Model で一括）

- `gravity_IsSettled` / `all_grounded_settle_foldl`: iterate-until-settled モデルで定義的に成立
- `process_*_placeAbove_settled` 2件: per-wave 等変性 + 反復帰納法で導出
- `IsSettled_liftUp_generatePins`: ピン生成の接地性保存を構成的証明で置換

### axiom 採用の経緯

sorry #4b（`all_grounded_settle_foldl` 内 pin NE コールバック）に対して 11アプローチを消耗。
sorry #3/#4b に5-8セッションが必要と判断し、外部依存ゼロの両 sorry を axiom 化（Plan B）。
~8,000行の sorry-free 証明資産は完全保全。詳細: [偽定理カタログ](../s2il/false-theorem-catalog.md)

---

## §3 Wave Gravity Model（axiom 除去ロードマップ）

現行 foldl モデルを `iterate waveStep until floatingUnits = []` に置き換え、axiom 5件を除去する。

### タスク

| タスク | 推定行数 | 推定工数 |
|---|---|---|
| `Gravity.process` 再定義 | ~100-200 | 0.5 s |
| 終端性証明（FU 長さ厳密減少） | ~200-400 | 1-2 s |
| 等変性再証明（per-wave + 反復帰納法） | ~300-600 | 1-2 s |
| axiom 除去（構成的証明で置換） | ~50 | 0.1 s |
| PermInvariance 削減評価 | 要調査 | 0.5 s |
| **合計** | **~650-1250** | **3-5 s** |

### PermInvariance 削減の可能性

| 方式 | PermInvariance | 削減量 |
|---|---|---|
| 各 wave 内で foldl + ソート | 引き続き必要 | 0 |
| 層別同時処理 | **不要** | ~6,600 行削減可能 |

### 既存資産との関係

- `settle_foldl_eq` Phase 1/2 等変性: per-wave 等変性の基盤として再利用可能
- `settleStep_comm_dir_gap` / `settleStep_comm_ne_dir`: minLayer ペアの可換性は引き続き有効
- Equivariance_obsolated.lean / CommExt_obsolated.lean: foldl → iterate 移行時に Phase 3 置換が必要

### 3.1 波動モデル（Wave Gravity）への将来的移行検討

#### 波動モデルの概要

現行の foldl モデルでは FU を `sortFallingUnits'` でソートし、1 個ずつ順次着地させる。波動モデルでは全 FU を同時に 1 レイヤずつ落下させ、着地したものから除外する反復方式をとる。

```text
Wave Model:
  1. floatingUnits(shape) で不安定ユニットを特定
  2. 安定要素のみに接触する FU を即座に settle（接地化）
  3. 残りの FU を全て 1 レイヤ下に移動
  4. 安定するまで 2-3 を繰り返し
```

#### 数学的等価性

- `settle_foldl_eq`（SettleFoldlEq.lean, ~4,300 行）が既に foldl モデルと波動モデルの等価性を証明済み
- ステップ 3（1 レイヤ同時降下）は幾何制約により実際には発火しない。全 FU は着地位置に直接 settle される
- したがって波動モデルを採用しても、結果は foldl モデルと完全に一致する

#### 移行のメリット・デメリット

| 項目 | 評価 |
|---|---|
| ソート不要（PermInvariance ~2,300 行が不要に） | ✅ 大幅削減 |
| SettleFoldlEq ~4,300 行が不要に | ✅ 大幅削減 |
| sorry #4b は解消されない（着地位置の性質であり順序非依存） | ❌ 効果なし |
| 既存証明資産（Equivariance, CommExt 等）の全面書き換え | ❌ 高コスト |

#### ≥6L 問題への対応ポテンシャル（2026-04-13 考察）

sorry #3 の根本原因は「placeAbove 後の ≥6L shapes で foldl ソート可換性が成立しない」ことにある。波動モデルは FU をソートせず、全 FU を層単位で同時処理するため、このソート順序依存性が消滅する。理論上、波動モデルでは `layerCount ≤ 5` 制約も `IsSettled` 仮説も不要で、placeAbove 後の gravity 等変性を証明できる可能性がある。一方、sorry #4b（pin NE 時点の ImmBelow）は着地位置の性質であり順序非依存のため、波動モデルへの移行では解消されない。

| sorry | foldl モデル（現行） | 波動モデル（将来） |
|---|---|---|
| #4b (pin NE ImmBelow) | 解消未達（現状） | 解消されない（順序非依存の性質） |
| #3 (stack_rotate180_comm) | `IsSettled` 仮説が必要 | ≥6L 問題が消滅する可能性（ソート順序依存性が消滅） |

#### BFS 修正後の FU=0 維持ケース（2026-04-13 考察）

BFS を上方向のみに修正した後も、垂直チェーンが存在する場合は FU=0 が維持される。

| シェイプ | 修正前 FU | 修正後 FU | 接地維持の理由 |
|---|---|---|---|
| `CuCu----:CuP-----:CuCu----` | FU=0 | FU=0（変化なし） | L0:SE(Cu)→L1:SE(P)→L2:SE(Cu) の垂直チェーンで上方向 BFS 到達可 |

L1:SE のピンは L0:SE（copper, 非空）から上方向接地接触で BFS 到達可能。修正後の上方向 BFS でも「L0:SE → L1:SE(P) → L2:SE(Cu)」の垂直チェーン全体が接地済みと判定され、FU=0 のまま変化しない。これに対し S1〜S4（`Rr------:RrP-----:RrRr----` 等）は L0:SE が空のため垂直チェーンが切断されており、修正後に FU>0 となる。

### 3.2 Wave Gravity Model 完了後の最終点検

§3 のタスク完了後に、以下の観点で数学的・コード的美しさの最終点検を行う。

| 確認項目 | 基準 |
|---|---|
| 冗長な場合分けの排除 | 構造的な帰納法やジェネリック補題で代替可能か |
| 補題の一般性 | 不要な仮説が付いていないか |
| 命名規約 | S2IL 固有ルール + Lean 4 / Mathlib 命名規則 |
| doc コメント | public def/theorem に日本語 `/-- ... -/` が付与されているか |

---

## §4 確立済みの基盤

### 重要な発見と根拠

| 事実 | 根拠 |
|---|---|
| `process_rotate180` は ≤5L で真 | 1.9M+ shapes 計算検証 |
| `process_rotate180` は ≥6L で偽 | 反例: `"cr----cr:cr------:--------:cr--cr--:--crcr--:crcrcr--"`（同 minLayer FU でソート順序が結果に影響） |
| `process_rotate180` は placeAbove 構造で真 | 166K shapes (6-10L 含む, 0 failures) |
| `process_rotateCW` は真 | 65K+ shapes 計算検証 |
| ≥6L 反例はゲーム内で到達不可能 | Stacker 1st gravity の入力は常に settled |
| `IsSettled` は `layerCount ≤ 5` の代替仮説として有効 | 166,757+ settled shapes で 0 failures |

### 各加工装置の gravity 利用パターン

| 加工装置 | gravity 利用 | layerCount ≤ 5? | IsSettled 必要? |
|---|---|---|---|
| Painter / CrystalGenerator / Rotator / ColorMixer | なし | — | N/A |
| PinPusher | `truncated.gravity` | ≤ maxLayers ≤ 5 ✅ | 不要 |
| **Stacker (1st gravity)** | `afterShatter.gravity` | ≤ 2×maxLayers ❌ | **必要** |
| Stacker (2nd gravity) | `truncated.gravity` | ≤ maxLayers ≤ 5 ✅ | 不要 |
| Cutter / HalfDestroy / Swap | `settleAfterCut` 内 | ≤ maxLayers ≤ 5 ✅ | 不要 |

詳細: [gravity-issettled-matrix.md](../s2il/gravity-issettled-matrix.md)

### stress8 (maxLayers > 5) への拡張

現行の `layerCount ≤ 5` 仮説は vanilla4/5 でのみ有効。stress8 では全装置で IsSettled アプローチが必要。現時点では優先度外。

### 採用アプローチ: 全順序ソート

`fallingUnitOrd` 全順序でソート結果を一意化。基盤はすべて完了:
- `fallingUnitOrd` 全順序: `_total`, `_trans`, `_antisymm_of_floatingUnits_impl` ✅
- `mergeSort_perm_eq` ✅
- `settle_foldl_eq` Phase 1/2（r180/rCW 両方）✅

---

## §5 完了済み作業の要約

### 主要完了項目

| 項目 | 内容 | 結果 |
|---|---|---|
| isGroundingContact バグ修正 | `groundingBfs` の探索辺を `isUpwardGroundingContact || isStructurallyBonded` に修正 | sorry 6→2 |
| Plan B（axiom 化） | 外部依存ゼロの難所を axiom 化し証明チェーンを前進 | sorry 2→0（axiom 3→5） |
| SettledShape 完了 | rotate/pinPush/stack/swap を含む全操作で SettledShape 化 | Machine.lean まで適用完了 |
| rCW 等変性 + LayerPerm 統合 | rCW 経路の重複を統合しジェネリック化を推進 | 3ファイル合計 -128 行純減 |
| simp 安定化 | `lean --json` + `simp?` で自動安定化 | 76箇所を `simp only` / `simp_all only` 化 |
| 証明品質リファクタリング | R-1〜R-14 と F-1/F-3 を実施 | 高・中・低優先度項目を完了 |

### 履歴ハイライト

| Wave / フェーズ | 概要 | sorry 推移 |
|---|---|---|
| Wave 9 | `settleStep_comm_dir_gap` 解消 | 7→5 |
| Wave 19 | sorry #4a 削除 + pin 空着地証明 | 5→3 |
| Wave 21 | sorry #4c + pin d≥2 解消 | 3→2 |
| combined edge 修正 | grounding edge 実装修正 | 6→2 |
| Plan B | axiom 化で証明完了状態へ移行 | 2→0 |

---

## 関連ドキュメント

| ドキュメント | 概要 |
|---|---|
| [MILESTONES.md](MILESTONES.md) | マイルストーン チェックシート |
| [偽定理カタログ](../s2il/false-theorem-catalog.md) | Plan A で発見された偽定理・棄却済みアプローチ一覧 |
| [gravity-equivariance-analysis.md](../s2il/gravity-equivariance-analysis.md) | Gravity 証明の技術的知見 |
| [gravity-issettled-matrix.md](../s2il/gravity-issettled-matrix.md) | 全加工装置の gravity 利用・IsSettled 必要性マトリクス |
| [s2il-lemma-index.md](../s2il/s2il-lemma-index.md) | 補題インデックス |







