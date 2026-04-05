# 証明リファクタリング計画

> 対象: `S2IL/` 配下の全 `.lean` ファイル（`Gravity.lean` の `process_rotate180` 証明チェーンを除く）
> 作成日: 2026-04-05
> 最終更新: 2026-04-06

---

## 0. 完了サマリー

Wave 0–4 の simp only 安定化・レイヤ数制約撤廃・ドキュメント改善は**全て完了**。
詳細は [付録 A](#付録-a-完了済み-wave-04-の記録) を参照。

| 指標 | 実施前 | 現状 |
|---|---|---|
| 裸 `simp`（Gravity 除外） | 183 個 | **0 個** ✅ |
| `simp_all`（不安定） | 4 個 | **1 個** (QuarterPos.lean, Mathlib 依存で据置) |
| レイヤ数制約引数 | 3 個 | **0 個** ✅ |
| `falling.md` の安定状態記載 | なし | **追加済み** ✅ |
| `crystal-shatter.md` 実装反映 | 未反映 | **反映済み** ✅ |

---

## 1. 残課題一覧

### 1.1 証明品質の改善（将来課題）

| # | 対象 | 内容 | 難度 |
|---|---|---|---|
| R-1 | QuarterPos.lean | `clearPositions_ext` (66 行) の補題分割 | ★★★ |
| R-2 | Shape.lean | `ofString_toString` (41 行) の補題分割 | ★★ |
| R-3 | GenericBfs.lean | `genericBfs_queue_in_result` (75 行超) の分割 | ★★★ |
| R-4 | CrystalBond.lean | `bfs_sound` (70 行超) の分割 | ★★★ |
| R-5 | GenericBfs.lean | Bool 分岐の簡潔化（`tauto` / `omega` 活用） | ★★ |
| R-6 | CrystalBond.lean | `cases` 4 段ネスト → `decide` / `fin_cases` | ★★ |
| R-7 | QuarterPos.lean | Direction 分岐の `fin_cases` / `decide` 検討 | ★ |
| R-8 | QuarterPos.lean | 残り 1 箇所の `simp_all`（Mathlib 未インポート） | ★ |

### 1.2 設計・属性の見直し（将来課題）

| # | 対象 | 内容 | 難度 |
|---|---|---|---|
| D-1 | 全ファイル | `@[simp]` 属性の設計基準適用レビュー | ★★ |
| D-2 | 全ファイル | ファイル先頭コメント統一 | ★ |
| D-3 | CrystalBond / Shatter | rotate180 等変性テンプレートの共通化 (`Rotate180Lemmas.lean`) | ★★★ |

### 1.3 安定状態 (Settled State) の反映（将来課題）

| # | 内容 | 難度 |
|---|---|---|
| SS-1 | `paint_preserves_settled` の証明 | ★ |
| SS-2 | `crystallize_preserves_settled` の証明 | ★ |
| SS-3 | `rotateCW_preserves_settled` の証明 | ★★ |
| SS-4 | `gravity_produces_settled` の証明（基盤） | ★★★ |
| SS-5 | `IsSettled` の Gravity.lean からの分離検討 | ★★ |
| SS-6 | `SettledShape` サブタイプの導入検討 | ★★★ |

### 1.4 `@[simp]` 設計基準（参照用）

| 付与する | 付与しない |
|---|---|
| 正規化方向の等式（`rotate180_rotate180 = id`）| 条件付き等式（仮定が複雑なもの） |
| 構造保存の等式（`isEmpty_rotateCW`）| 展開方向が明確でないもの |
| 冪等性（`crystallize_idempotent`）| 双方向に使える等式 |
| 吸収律（`mix_white_left`）| ループの危険があるもの |

---

## 2. リスク・注意事項

| リスク | 対策 |
|---|---|
| 補題分割で名前空間が汚染される | `private` を積極活用。公開 API を最小に |
| @[simp] 追加で既存証明が壊れる | 追加前に `lake build` でリグレッションチェック |
| IsSettled 前提追加で下流が壊れる | **定理（theorem）への追加のみ**。定義（def）は変更しない方針 |

---

## 3. Gravity.lean との境界

以下の補題は Gravity.lean が依存しているため、名前変更時は影響範囲を確認すること:

- `QuarterPos.rotate180_rotate180`
- `QuarterPos.clearPositions_ext`
- `QuarterPos.setQuarter_empty_comm`
- `Shape.rotate180`, `Shape.mapLayers`
- `Layer.rotate180`, `Layer.isEmpty_rotate180`
- `CrystalBond.*` (structuralClusterList 関連)
- `Shatter.shatterOnCut_rotate180_comm`, `shatterOnFall_rotate180_comm`
- `GenericBfs.*` (BFS 健全性定理)

※ 型シグネチャの変更禁止制約は Wave 0–4 完了に伴い**解除済み**。
  名前変更を含むリファクタリングが可能（ただし Gravity.lean 側の参照も同時に更新すること）。

---

## 4. 参考情報

| 参照 | 用途 |
|---|---|
| `.github/skills/lean-simp-guide/SKILL.md` | simp 系タクティクの使い分け・安定化移行ガイド |
| `.github/skills/lean-tactic-select/SKILL.md` | ゴール形状 → タクティク選定 |
| `.github/skills/lean-repl/SKILL.md` | REPL での simp? 実行手順 |
| `docs/knowledge/lean-proof-tips.md` | simp only 原則・タクティク使い分け |

---

## 付録 A: 完了済み Wave 0–4 の記録

以下は 2026-04-05 に実施完了した作業の要約。

### Wave 0: 設計見直し（コミット `48d25ae`）

- `Shape.stack` / `Shape.pinPush` のレイヤ数制約引数を削除
- `Machine.lean` の `if h : layerCount ≤ ...` 分岐を除去
- `falling.md` に「安定状態と落下処理」セクションを追加
- `crystal-shatter.md` の実装状況を反映
- `Machine.lean` に安定状態方針コメントを追加

### Wave 1: 基盤 Shape 層（コミット `e2a8a60`）

| ファイル | 裸 simp | simp_all | 備考 |
|---|---|---|---|
| Rotate.lean | 18 → 0 | — | |
| QuarterPos.lean | 17 → 0 | 2 → 1 | 1 件は手動証明化、1 件は Mathlib 依存で据置 |
| Shape.lean | 11 → 0 | — | |

### Wave 2: BFS 関連（コミット `2b4829e`）

| ファイル | 裸 simp | 備考 |
|---|---|---|
| GenericBfs.lean | 31 → 0 | |
| CrystalBond.lean | 45 → 0 | |

### Wave 3: 加工操作（コミット `763a3af`）

| ファイル | 裸 simp | simp_all | 備考 |
|---|---|---|---|
| Shatter.lean | 15 → 0 | 1 → 0 (simp_all only 化) | |
| Cutter.lean | 6 → 0 | 1 → 0 (simp_all only 化) | |
| CrystalGenerator.lean | 2 → 0 | — | |
| Painter.lean | 3 → 0 | — | |
| PinPusher.lean | 3 → 0 | — | |
| Stacker.lean | 2 → 0 | — | |
| Rotate180Lemmas.lean | 3 → 0 | — | |

### Wave 4: 仕上げ（コミット `b58be6c`）

| ファイル | 裸 simp | 備考 |
|---|---|---|
| GameConfig.lean | 1 → 0 | |

### 旧定量分析（実施前スナップショット）

| ファイル | 行数 | 定理数 | 旧 裸 simp | 旧 simp only | 旧 simp_all | @[simp] | sorry |
|---|---|---|---|---|---|---|---|
| CrystalBond.lean | 963 | 43 | 45 | 50 | 0 | 0 | 0 |
| GenericBfs.lean | 501 | 14 | 29 | 25 | 0 | 0 | 0 |
| Rotate.lean | 164 | 4 | 39 | 0 | 0 | 21 | 0 |
| QuarterPos.lean | 396 | 22 | 18 | 11 | 2 | 2 | 0 |
| Shatter.lean | 415 | 21 | 15 | 19 | 1 | 0 | 0 |
| Shape.lean | 328 | 15 | 9 | 15 | 0 | 0 | 0 |
| Cutter.lean | 275 | 23 | 8 | 7 | 1 | 2 | 0 |
| CrystalGenerator.lean | 57 | 2 | 5 | 0 | 0 | 3 | 0 |
| Painter.lean | 59 | 3 | 6 | 0 | 0 | 3 | 0 |
| Rotate180Lemmas.lean | 111 | 9 | 3 | 5 | 0 | 0 | 0 |
| Stacker.lean | 78 | 1 | 2 | 0 | 0 | 0 | 0 |
| PinPusher.lean | 67 | 1 | 3 | 0 | 0 | 0 | 0 |
| Color.lean | 195 | 6 | 0 | 0 | 0 | 0 | 0 |
| GameConfig.lean | 85 | 4 | 1 | 1 | 0 | 0 | 0 |
| Layer.lean | 83 | 2 | 0 | 2 | 0 | 0 | 0 |
| PartCode.lean | 118 | 3 | 0 | 0 | 0 | 0 | 0 |
| Quarter.lean | 86 | 1 | 0 | 0 | 0 | 0 | 0 |

**合計（Gravity.lean 除外）**: 裸 simp **183 個** → **0 個**