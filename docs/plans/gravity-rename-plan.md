# Gravity.lean 命名リファクタリング計画

> 作成日: 2026-04-06
> 対象: `S2IL/Behavior/Gravity.lean` + `S2IL/Behavior/GenericBfs.lean`

---

## 0. 背景

Wave 0–4 の完了に伴い、Gravity.lean との境界 API に対する「型シグネチャの変更禁止」制約を解除する。
本計画では、命名規約違反や略語の不統一を修正し、コードの可読性と一貫性を向上させる。

---

## 1. リネーム対象一覧

### 1.1 略語の統一（`sortFU` → `sortFallingUnits`）

| 現在の名前 | 提案 | ファイル |
|---|---|---|
| `sortFU_inversion_is_tied` | `sortFallingUnits_inversion_is_tied` | Gravity.lean |
| `sortFU_inversion_dir_disjoint` | `sortFallingUnits_inversion_dir_disjoint` | Gravity.lean |
| `sortFU_foldl_perm_input_eq` | `sortFallingUnits_foldl_perm_input_eq` | Gravity.lean |

### 1.2 略語の統一（`fU` → `floatingUnits`）

| 現在の名前 | 提案 | ファイル |
|---|---|---|
| `fU_elem_positions_disjoint` | `floatingUnits_elem_positions_disjoint` | Gravity.lean |
| `fU_bonded_positions_absurd` | `floatingUnits_bonded_positions_absurd` | Gravity.lean |
| `fU_cluster_in_allStructuralClustersList` | `floatingUnits_cluster_in_allStructuralClustersList` | Gravity.lean |

### 1.3 略語の統一（`spb` → `shouldProcessBefore`）

| 現在の名前 | 提案 | ファイル |
|---|---|---|
| `spb_false_minLayerAtDir_ge` | `shouldProcessBefore_false_minLayerAtDir_ge` | Gravity.lean |
| `spb_true_witness` | `shouldProcessBefore_true_witness` | Gravity.lean |
| `spb_no_mutual` | `shouldProcessBefore_no_mutual` | Gravity.lean |
| `spb_no_chain` | `shouldProcessBefore_no_chain` | Gravity.lean |
| `insertSorted_before_spb` | `insertSorted_before_shouldProcessBefore` | Gravity.lean |
| `insertSorted_append_when_no_spb` | `insertSorted_append_when_no_shouldProcessBefore` | Gravity.lean |
| `foldl_insertSorted_preserves_spb_order` | `foldl_insertSorted_preserves_shouldProcessBefore_order` | Gravity.lean |

### 1.4 `σ_ic` 系（ギリシャ文字・不明瞭な略語）

| 現在の名前 | 提案 | 種別 |
|---|---|---|
| `σ_ic` | `swapIndex` | def |
| `σ_ic_invol` | `swapIndex_invol` | theorem |
| `σ_ic_lt_of_lt` | `swapIndex_lt_of_lt` | theorem |
| `σ_ic_preserves_lt` | `swapIndex_preserves_lt` | theorem |
| `σ_ic_pair_ne` | `swapIndex_pair_ne` | theorem |
| `pairsList_ic` | `pairsList` | def |
| `mem_pairsList_ic` | `mem_pairsList` | theorem |
| `pairsList_ic_nodup` | `pairsList_nodup` | theorem |
| `σ_pair_ic` | `swapPair` | def |
| `getElem_swap_σ_ic` | `getElem_swap_swapIndex` | theorem |
| `invCount_eq_pairsFoldl_ic` | `invCount_eq_pairsFoldl` | theorem |

### 1.5 `GenericReachable_*` の大文字開始修正

| 現在の名前 | 提案 | ファイル |
|---|---|---|
| `GenericReachable_trans` | `genericReachable_trans` | Gravity.lean |
| `GenericReachable_reverse` | `genericReachable_reverse` | Gravity.lean |
| `GenericReachable_mono` | `genericReachable_mono` | Gravity.lean |

### 1.6 境界 API の修正

| 現在の名前 | 提案 | ファイル | 影響 |
|---|---|---|---|
| `GenericBFSInv` | `GenericBfsInv` | GenericBfs.lean | Gravity.lean で 1 箇所参照 |

---

## 2. ドキュメント更新対象

リネーム実施後、以下のドキュメント内の旧名を新名に更新する:

| ドキュメント | 更新が必要な名前 |
|---|---|
| `docs/plans/gravity-proof-cheatsheet.md` | `spb_*`, `sortFU_*`, `fU_*` |
| `docs/knowledge/gravity-equivariance-analysis.md` | `spb_*`, `sortFU_*`, `shouldProcessBefore` |
| `docs/knowledge/settle-foldl-eq-analysis.md` | `spb_*`, `sortFU_*`, `fU_*` |
| `/memories/repo/gravity-rotate180-proof-status.md` | `spb_*`, `sortFU_*` |

---

## 3. 実行手順

1. **GenericBfs.lean**: `GenericBFSInv` → `GenericBfsInv`（定義 + 全参照）
2. **Gravity.lean**: `σ_ic` 系 12 件を一括置換（全て private、外部影響なし）
3. **Gravity.lean**: `GenericReachable_*` 3 件を小文字開始に置換
4. **Gravity.lean**: `fU_*` 3 件を `floatingUnits_*` に展開
5. **Gravity.lean**: `sortFU_*` 3 件を `sortFallingUnits_*` に展開
6. **Gravity.lean**: `spb_*` 7 件を `shouldProcessBefore_*` に展開
7. **`lake build`** で全体のリグレッションチェック
8. **ドキュメント 4 ファイル** の旧名を新名に更新
9. **`gravity-proof-cheatsheet.md` Section 0** のレイヤ制約お知らせを「撤廃済み」に更新

### チェックリスト

- [ ] `GenericBFSInv` → `GenericBfsInv`（GenericBfs.lean + Gravity.lean）
- [ ] `σ_ic` 系 12 件（Gravity.lean 内部のみ）
- [ ] `GenericReachable_*` 3 件（Gravity.lean 内部のみ）
- [ ] `fU_*` 3 件（Gravity.lean 内部のみ）
- [ ] `sortFU_*` 3 件（Gravity.lean 内部のみ）
- [ ] `spb_*` 7 件（Gravity.lean 内部のみ）
- [ ] `lake build` 通過
- [ ] `gravity-proof-cheatsheet.md` の名前更新 + Section 0 更新
- [ ] `gravity-equivariance-analysis.md` の名前更新
- [ ] `settle-foldl-eq-analysis.md` の名前更新
- [ ] `/memories/repo/gravity-rotate180-proof-status.md` の名前更新

---

## 4. リスク

| リスク | 対策 |
|---|---|
| 大量置換で参照漏れ | grep で旧名が残っていないか検証 |
| `spb` → `shouldProcessBefore` で名前が長大化 | 証明本体では `have h_spb := ...` のように局所変数で略称を使用して可 |
| 私的定理 (`private`) の変更が不完全 | Gravity.lean は private 定理が多数だが、同ファイル内完結のため grep + build で検証可能 |

---

## 5. 対象外

以下は現時点でリネーム不要と判断:

- 境界 API の大部分（`QuarterPos.rotate180_rotate180` 等）: 既に命名規約に準拠
- `eqPred` / `invCount` / `posIn`: 規約準拠、十分に記述的
- `shouldProcessBefore` 自体の定義名: 既にフルネームで規約準拠
