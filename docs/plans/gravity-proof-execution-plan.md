# Gravity 証明チェーン見直し — 最終実行計画

> 作成日: 2026-04-05
> 分析文書: [`process-rotate180-proof-redesign.md`](process-rotate180-proof-redesign.md)（提案の比較・詳細ロードマップ）

---

## 0. 概要

### 採用戦略: 3 段階アプローチ

| フェーズ | 提案 | 目標 | 時間軸 |
|---|---|---|---|
| **短期** | **提案 B**: 直接 direction-disjoint 証明 | `process_rotate180` のブロッキング解消 | Phase 1 |
| **中期** | **提案 D**: 決定性ソート移行 | rotateCW 等変性の自動導出・保守性向上 | Phase 1.5〜2 |
| **長期** | **提案 C**: 正準着地位置（オプショナル） | MaM ソルバー健全性・gravity 冪等性 | Phase 3 |

決定根拠は [`process-rotate180-proof-redesign.md` Section 5.4](process-rotate180-proof-redesign.md) を参照。

### ドキュメント整理方針

本計画と併せて以下のドキュメント整理を実施する:

| ファイル | 方針 |
|---|---|
| `gravity-proof-cheatsheet.md` | **廃止** — 内容を補題インデックス (T-2)・知見ドキュメント・本計画に振り分け |
| `gravity-simp-plan.md` | **廃止** — コンセプトを本計画 Wave 4 に取り込み、ファイル削除 |
| `process-rotate180-proof-redesign.md` | **維持** — 提案の分析・比較表として参照用に残す |
| `proof-cleanup-plan.md` | **維持** — Gravity 以外のリファクタリング状態管理を継続 |

---

## 1. マイルストーン全体マップ

```
Wave 0: ドキュメント整理 (T-2, T-3)
  ↓
Wave 1: SettledState 完了 (SS-2〜SS-4)
  ↓
Wave 2: process_rotate180 真理値再検証 (4L+)
  ↓
Wave 3: 提案 B — process_rotate180 証明チェーン再構築
  ↓
Wave 4: Gravity.lean simp only 安定化 (旧 gravity-simp-plan)
  ↓
Wave 5: 下流 r180 等変性 (stack, pinPush, paint, crystallize)
  ↓ ─── Phase 1 完了ライン ───
Wave 6 [中期]: 提案 D — 決定性ソート移行
  ↓
Wave 7 [長期]: 提案 C — 正準着地位置（オプショナル）
```

---

## 2. Wave 0: ドキュメント整理

`gravity-proof-cheatsheet.md` の情報が今後の作業で流動的になるため、
混乱を避けて情報の切り分けと整理を先行実施する。

### 2.1 T-2: 補題インデックスの整備

`docs/lean/s2il-lemma-index.md` を新設し、Gravity.lean の証明済み補題を索引化する。

- [ ] **0-1**: `docs/lean/s2il-lemma-index.md` の雛形作成
- [ ] **0-2**: cheatsheet Section 7（ファイル構造マップ）の内容を移行
- [ ] **0-3**: cheatsheet Section 8（確立済みの事実）の内容を移行
- [ ] **0-4**: cheatsheet Section 3（sorry 一覧）の確定情報を移行
- [ ] **0-5**: cheatsheet Section 11（テスト一覧）の内容を移行

**振り分け先の構成案**:
```markdown
# S2IL 補題インデックス
## Gravity.lean
### ファイル構造マップ        ← Section 7
### 主要定理・補題一覧        ← 新規整理
### テストファイル一覧        ← Section 11
## SettledState.lean
## Rotate180Lemmas.lean
## （他ファイルは段階的に追加）
```

### 2.2 T-3: 等変性証明パターン集の整備

既存の個別 knowledge を統合し、等変性証明の汎用パターン集を作成する。

- [ ] **0-6**: `docs/knowledge/equivariance-proof-patterns.md` の新設
- [ ] **0-7**: `gravity-equivariance-analysis.md` の汎用パターンを抽出・統合
- [ ] **0-8**: `bfs-equivariance-proof.md` の汎用パターンを抽出・統合
- [ ] **0-9**: `settle-foldl-eq-analysis.md` の汎用パターンを抽出・統合

**パターン集の構成案**:
```markdown
# 等変性・交換則 証明パターン集
## パターン 1: pointwise any 等価 → foldl 等価
## パターン 2: Perm + 隣接可換 → foldl 等価（バブルソート帰納法）
## パターン 3: BFS 列挙の等変性（.any メンバーシップ）
## パターン 4: direction-disjoint → settleStep 可換
## パターン 5: operator ∘ rotate = rotate ∘ operator 型の等変性
```

### 2.3 cheatsheet 残存情報の振り分け

- [ ] **0-10**: cheatsheet Section 9（偽定理カタログ）を `docs/knowledge/lean-proof-tips.md` に移行
    - 「Gravity 証明で判明した偽定理」セクションとして追記
- [ ] **0-11**: cheatsheet Section 13（修正計画）は `process-rotate180-proof-redesign.md` に既に統合済みであることを確認

### 2.4 gravity-simp-plan.md の統合と削除

`gravity-simp-plan.md` の内容は Wave 3 完了後に対象が大幅に変わるため、
コンセプトのみ本計画 Wave 4 に取り込み、ファイルを削除する。

- [ ] **0-12**: gravity-simp-plan.md のコンセプト（パターン分類・Phase 構成）を Wave 4 に反映済みであることを確認
- [ ] **0-13**: `gravity-simp-plan.md` を削除

### 2.5 ドキュメント参照の更新

- [ ] **0-14**: `.github/copilot-instructions.md` の「証明チートシート」参照を更新
    - `gravity-proof-cheatsheet.md` → 本計画 + `s2il-lemma-index.md` + `process-rotate180-proof-redesign.md`
- [ ] **0-15**: `gravity-proof-cheatsheet.md` を削除（全content 移行完了後）
- [ ] **0-16**: `docs/plans/README.md` のファイル一覧を更新

---

## 3. Wave 1: SettledState 完了

`process_rotate180` の証明は SettledState 基盤に依存しないが、
下流の `stack_rotate180_comm` 等は `gravity_IsSettled` を必要とする可能性がある。
先行して完了させることで Phase 1 全体の見通しを確保する。

- [ ] **1-1**: SS-2 `IsSettled_crystallize` の証明（`floatingUnits_crystallize_eq` が核心）
- [ ] **1-2**: SS-3 `IsSettled_rotateCW` の証明（`floatingUnits_isEmpty_rotateCW` が核心）
- [ ] **1-3**: SS-4 `gravity_IsSettled` の証明（★★★ — `process` 出力が安定状態であることの最重要定理）
- [ ] **1-4**: SS-6 `SettledShape` サブタイプの導入検討（SS-1〜SS-4 完了後）
- [ ] **1-5**: `proof-cleanup-plan.md` の SS 状態を更新

---

## 4. Wave 2: process_rotate180 真理値再検証

S-5 反例が 4L で発見された教訓を踏まえ、4L+ での網羅的検証を実施する。
**提案 B の証明着手前に完了すること**（偽定理への工数浪費を防止）。

- [ ] **2-1**: 4L 全形状の穷举検証スクリプト作成（`Scratch/ProcessRotate180Check4L.lean`）
- [ ] **2-2**: 4L 穷举検証の実行・結果確認（failures = 0 を確認）
- [ ] **2-3**: 構造的カバレッジ確認（空レイヤ混在・大規模クラスタ・複数チェーン・ピン集中・混合方角）
- [ ] **2-4**: 5L+ ランダムサンプリング（10,000 件、`Scratch/ProcessRotate180Random.lean`）
- [ ] **2-5**: 検証結果を `s2il-lemma-index.md` の Gravity セクションに記録

---

## 5. Wave 3: 提案 B — process_rotate180 証明チェーン再構築

提案 B「直接 direction-disjoint 証明」を実施し、唯一の sorry を解消する。
詳細は [`process-rotate180-proof-redesign.md` Section 8](process-rotate180-proof-redesign.md) を参照。

### 5.1 準備

- [ ] **3-1**: 不健全コード（S-5 依存の ~380 行）をコメントでマーキング
- [ ] **3-2**: 削除対象の補題一覧を最終確認
    - `shouldProcessBefore_no_chain` (~20 行)
    - `foldl_insertSorted_preserves_spb_order` (~200 行)
    - `sortFallingUnits_spb_order_preserving` (~40 行)
    - `sortFallingUnits_inversion_is_tied` (~40 行, 新版で置換)
    - `sortFallingUnits_inversion_dir_disjoint` (~50 行, 新版で置換)
    - `sortFallingUnits_foldl_perm_input_eq` (~30 行, 新版で置換)

### 5.2 核心補題の証明

- [ ] **3-3**: `input_inversion_is_tied_r180` の証明（★★★）
    - l_mid と l2 の差分が tied ペアのスワップのみであることを r180 固有構造から導出
    - spb 保存性: `spb(a,b) = spb(g a, g b)` (r180 はレイヤ不変)
    - one-way pair は両入力で同順 → 入力反転は tied のみ
- [ ] **3-4**: `sortFU_tied_input_implies_tied_output` の証明（★★）
    - 入力反転が全て tied → insertSorted 出力の反転も全て tied
    - `insertSorted_preserves_relative_order` (S-2, 完了) を活用
- [ ] **3-5**: `sortFU_output_inversion_dir_disjoint_r180` の組み立て（★）
    - 3-3 + 3-4 + `tied_no_shared_dir` → direction-disjoint

### 5.3 統合

- [ ] **3-6**: `settle_foldl_eq` Phase 2 の書き換え
    - `foldl_eq_of_perm_tied_adj_comm` + 新版 `sortFU_output_inversion_dir_disjoint_r180` を接続
- [ ] **3-7**: 不健全コードの削除
- [ ] **3-8**: `lake build` 通過（errors = 0, sorry = 0）
- [ ] **3-9**: `Test/Behavior/GravityRotate180.lean` の計算検証パス確認
- [ ] **3-10**: `process-rotate180-proof-redesign.md` の状態を「完了」に更新

---

## 6. Wave 4: Gravity.lean simp only 安定化

> 旧 `gravity-simp-plan.md` のコンセプトを取り込み。
> Wave 3 完了後の実際の残存数を再計測してから着手する。

### 6.1 コンセプト

Gravity.lean 内の裸 `simp` / `simp_all` を全て `simp only [...]` / `simp_all only [...]` に安定化し、
Mathlib 更新による証明破損リスクを排除する。

- Wave 3 で削除される ~380 行に含まれる裸 simp は対象外
- Wave 3 で新規作成されるコードは最初から `simp only` で記述

### 6.2 パターン分類（gravity-simp-plan.md より）

| パターン | 推定数 | 難度 | 手法 |
|---|---|---|---|
| `simp [lemmas]` | ~90 | ★☆☆ | `simp?` → `simp only` 直接置換 |
| `simp [lemmas] at h` | ~30 | ★☆☆ | 同上 |
| `simp at h` | ~31 | ★★☆ | `simp?` で補題特定が必要 |
| `<;> simp` | ~14 | ★★☆ | 分岐ごとに個別確認 |
| `by simp` (term-mode) | ~56 | ★☆☆ | 大半は自明性 |
| 完全裸 `simp` | ~21 | ★★★ | 個別調査必要 |
| `simp_all` | ~17 | ★★☆ | `simp_all?` で補題取得 |

### 6.3 実行計画

- [ ] **4-1**: Wave 3 完了後の裸 simp 残存数を再計測
- [ ] **4-2**: Phase 1 — バッチ処理可能パターンの安定化（`lean-simp-stabilizer` 活用）
- [ ] **4-3**: Phase 1 `lake build` 通過確認
- [ ] **4-4**: Phase 2 — セクション集中処理（foldl 可換性・バブルソート基盤・insertSorted）
- [ ] **4-5**: Phase 2 `lake build` 通過確認
- [ ] **4-6**: Phase 3 — 個別対応（BFS・Reachability・完全裸 simp）
- [ ] **4-7**: Phase 3 `lake build` 通過確認
- [ ] **4-8**: Gravity.lean の裸 simp = 0 を達成、`proof-cleanup-plan.md` を更新

---

## 7. Wave 5: 下流 r180 等変性

Wave 3 完了により `gravity_rotate180_comm` が利用可能になる。
これを用いて下流操作の r180 等変性を証明する。

- [ ] **5-1**: `stack_rotate180_comm` の証明（stack = placeAbove + shatter + gravity + truncate）
- [ ] **5-2**: `pinPush_rotate180_comm` の証明
- [ ] **5-3**: `paint_rotate180_comm` の証明（構造的に簡単、着色は BFS 無関係）
- [ ] **5-4**: `crystallize_rotate180_comm` の証明
- [ ] **5-5**: `cut_rotate180_comm` の sorry 解消確認（既に `gravity_rotate180_comm` に依存、自動的に解消）
- [ ] **5-6**: MILESTONES.md 1-2-4 の状態を更新
- [ ] **5-7**: 全 r180 等変性の `lake build` 確認

### ── Phase 1 完了ライン ──

Wave 5 完了をもって **MILESTONES.md Phase 1 の Shape Processing 等変性は完了**。
`process-rotate180-proof-redesign.md` のエグゼクティブサマリーを最終更新する。

---

## 8. Wave 6 [中期]: 提案 D — 決定性ソート移行

`sortFallingUnits` を Mathlib の `List.mergeSort` + 辞書式全順序に差し替え、
証明の保守性と将来の等変性拡張（rotateCW 等）を容易にする。

### 8.1 背景

- 現行の `sortFallingUnits` は `insertSorted` + `shouldProcessBefore`（半順序、tied ペアあり）
- tied ペアの入力順序依存性が証明の複雑さの根本原因
- 全順序化により tied ペアが消滅し、証明が大幅に簡素化される
- `spb` を拡張した全順序 `fuLe` を定義: `(layer, direction.toFin)` の辞書式比較
- Mathlib v4.29.0 の `List.mergeSort` を利用可能

### 8.2 実行計画

- [ ] **6-1**: `fuLe : FallingUnit → FallingUnit → Bool` の定義（辞書式比較）
- [ ] **6-2**: `fuLe` が全順序であることの証明（`DecidableLinearOrder` インスタンス）
- [ ] **6-3**: `sortFallingUnits' := List.mergeSort fuLe` の定義
- [ ] **6-4**: 移行証明 `sortFU_foldl_eq_sortFU'_foldl`: 新旧 sortFU の foldl 結果が一致
    - tied ペアの `placeFallingUnit` 可換性（`settleStep_comm_ne_dir`、既に証明済み）を利用
- [ ] **6-5**: `process` 定義を `sortFallingUnits'` に差し替え
- [ ] **6-6**: 既存証明のマイグレーション（`sortFallingUnits` → `sortFallingUnits'`）
- [ ] **6-7**: `process_rotateCW` の証明（mergeSort の Perm 不変性 + r(CW) 等変な全順序から自動導出）
- [ ] **6-8**: 不要になった tied 関連補題群の削除
- [ ] **6-9**: `lake build` 通過確認

---

## 9. Wave 7 [長期・オプショナル]: 提案 C — 正準着地位置

MaM ソルバーの健全性証明や gravity 冪等性が必要になった段階で着手する。
Phase 3 の進行中に必要性が明確化してから計画を具体化する。

### 9.1 構想

- `CanonicalLanding(s, fus) : Set QuarterPos` — 浮遊ユニット集合の正準着地位置
- 着地位置が入力の処理順序に依存しないこと（集合として一意）
- `process(s)` の出力がこの正準着地にユニットを配置した結果と一致すること

### 9.2 期待される副産物

- [ ] **7-1**: gravity 冪等性 `process (process s) = process s` の証明
- [ ] **7-2**: `gravity_IsSettled` (SS-4) の代替証明ルート
- [ ] **7-3**: MaM ソルバーの健全性基盤

---

## 10. 偽定理カタログ（cheatsheet Section 9 より承継）

以下の仮定は **全て偽** と判明済み。これらに依拠するアプローチを取ってはならない。
Wave 0 完了後は `docs/knowledge/lean-proof-tips.md` に移行される。

| 偽の仮定 | なぜ偽か |
|---|---|
| `shouldProcessBefore_no_chain` | 4L+ で 3 pin 連鎖反例。2-3L 限定検証の不備 |
| `sortFU_spb_order_on_fU` | 4 要素反例。insertSorted のグリーディ停止が順序を壊す |
| `sortFallingUnits_shouldProcessBefore_one_way_order` | spb 非推移性。3 要素反例 |
| `sortFU_later_not_spb_earlier` | 同根原因（非推移的 spb サイクル） |
| `sortFallingUnits_inversion_is_tied` (一般 Perm) | 3L 3色 8628 violations。r180 固有 Perm でのみ真 |
| sortFU が正しい topological sort を生成する | insertSorted はグリーディで後方不整合を生む |
| spb が floatingUnits 上で全順序 | tied ペアが存在する |
| BFS 列挙結果がリスト等号で r180 等変 | 探索順序が方角で変わる |
| `floatingUnits_rotate180` (list equality) | BFS order changes (.any メンバーシップのみ等変) |

---

## 11. 確立済みの事実（覆らない）

Wave 0 完了後は `docs/lean/s2il-lemma-index.md` に移行される。

| 事実 | 根拠 |
|---|---|
| `process_rotate180` は真 | 20+ テストケースで計算検証済み |
| spb は floatingUnits 上で DAG（2-cycle 禁止） | 計算検証 + `shouldProcessBefore_no_mutual` 証明済み |
| 方角素ペアは foldl で可換 | `settleStep_comm_ne_dir` 証明済み |
| tied ↔ direction-disjoint (floatingUnits 上) | 共有方角 → minLayer 差 → one-way → 対偶 |
| r180 はレイヤ不変、方角のみ NE↔SW / SE↔NW | `QuarterPos.rotate180` の定義 |
| spb(a,b) = spb(a.r180, b.r180) | r180 のレイヤ不変性から直接 |
| sortFU(l1).foldl = sortFU(l2).foldl (fU perms) | 計算検証 (23+ shapes, 2-3L 全形状) |
| l_mid/l2 の入力反転は常に tied | 同レイヤ・別方角ペアのみスワップ |

---

## 12. 健全コード資産（保持対象）

Wave 3 で安全に再利用できる既存コード。

| 補題 | 行数 | 用途 |
|---|---|---|
| `foldl_eq_of_perm_tied_adj_comm` | ~300 | バブルソート帰納法の本体 |
| `shouldProcessBefore_no_mutual` | ~200 | S-1、独立健全 |
| `insertSorted_preserves_relative_order` | ~150 | S-2、独立健全 |
| `tied_no_shared_dir` / `_rev` | ~100 | tied → direction-disjoint |
| `floatingUnits_elem_positions_disjoint` | ~100 | 位置素性 |
| `settleStep_comm_ne_dir` | ~200 | 方角素 → foldl 可換 |
| `sorted_foldl_pointwise_eq` | ~100 | settle_foldl_eq Phase 1 |
| `floatingUnit_any_in_rotate180` | ~50 | .any メンバーシップ等変 |
| その他基盤補題群 | ~4,000 | BFS・到達可能性・等変性基盤 |

---

## 13. 進捗サマリー

| Wave | 状態 | チェック数 | 完了数 |
|---|---|---|---|
| Wave 0: ドキュメント整理 | ⬜ 未着手 | 16 | 0 |
| Wave 1: SettledState 完了 | ⬜ 未着手 | 5 | 0 |
| Wave 2: 真理値再検証 | ⬜ 未着手 | 5 | 0 |
| Wave 3: 提案 B 実施 | ⬜ 未着手 | 10 | 0 |
| Wave 4: simp 安定化 | ⬜ 未着手 | 8 | 0 |
| Wave 5: 下流等変性 | ⬜ 未着手 | 7 | 0 |
| Wave 6: 提案 D [中期] | ⬜ 未着手 | 9 | 0 |
| Wave 7: 提案 C [長期] | ⬜ 未着手 | 3 | 0 |
| **合計** | | **63** | **0** |
