# 証明アプローチ候補レポート

> 作成日: 2026-03-31  
> 文脈: List→Finset 移行（Phases A–E）完了後、残 sorry 2 件の解消と将来の証明難度低減を目的とした調査

---

## 現状のビルド状態

- errors: 0 / sorries: 2 / warnings: 18
- 残 sorry:
  - `floatingUnits_spb_rank`（Gravity.lean）: spb が DAG → ランク関数の存在
  - `sortFU_foldl_perm_input_eq`（Gravity.lean）: floatingUnits 限定の Perm 不変性

---

## A. 残 sorry への直接アプローチ

### A-1. `floatingUnits_spb_rank` の証明

**概要**: `shouldProcessBefore` 関係が `floatingUnits s` 上で DAG（ランク関数が存在）であることを形式化する。

**難度**: ★★★★☆

**Mathlib 活用ポイント**:
- `Finset.card_lt_card` / `Finset.sum` — ランク計量の構成
- `Relation.Acyclic` — `Init` レベルで使える場合は循環なしの直接記述も可

**推奨手順**:

1. **Pin-Pin**: 同方角なら `minLayer` が全順序。異方角なら `spb = false`（発火しない）
2. **Pin-Cluster**: ピンは 1 方角のみ → その方角列の `minLayer` 大小で決まる
3. **Cluster-Cluster**: 最難所。以下の幾何制約を形式化する
   - `allStructuralClusters_disjoint` — 既証明。異クラスタは位置素
   - 「同レイヤ・隣接方角に別クラスタが共存不可」: 共存すれば構造結合でマージ → 矛盾
   - `structuralClusterList_sound` + `structuralClusterList_complete` — BFS 到達可能性インフラとして直接使用可

**ランク関数の候補**:
```lean
def spbRank (u : FallingUnit) : Nat :=
    Direction.all.foldl (fun acc d =>
        acc + match u.minLayerAtDir d with
        | some l => l + 1
        | none   => 0) 0
```
`spb(a,b) = true → spbRank a < spbRank b` を方角列ごとに示す。
Cluster-Cluster については幾何制約（同レイヤ方角排除）の形式化が前提となる。

---

### A-2. `sortFU_foldl_perm_input_eq` の証明

**概要**: A-1 完成後、`h_sub` による floatingUnits 限定の前提下で置換等価入力の foldl 結果一致を証明する。

**難度**: ★★★☆☆（A-1 完成が前提）

**方法 A（推奨）**:
1. `sortFU_preserves_spb_order_inFU`: floatingUnits 条件下の spb 順序保存（`insertSorted_split` + DAG + 幾何制約）
2. 反転ペアが全て tied → `tied_no_shared_dir` → `foldl_eq_of_perm_tied_adj_comm` を適用

**方法 C（代替）**:
- `floatingUnits_spb_rank` のランク関数で `rankSort` を定義
- `rankSort l = sortFU l`（floating限定）の uniqueness で結論

---

## B. 将来の証明難度低減アプローチ

### B-1. SimpleGraph 統合 — **棄却推奨**

**概要**: `GenericBfs`/`GenericReachable` を Mathlib の `SimpleGraph.Reachable` に置き換える。

**棄却理由**:
- `Fintype QuarterPos` が `GameConfig.layerCount` 依存 → `SimpleGraph.reachableSet` 等の Fintype 前提補題は利用不可
- `GenericBfs.lean` は健全性・完全性が既に完全証明済み
- 移行コストが効果を上回る

---

### B-2. `List.mergeSort` の部分活用

**概要**: `insertSorted`/`sortFallingUnits` を Mathlib の `List.mergeSort` に統一し、`List.Perm` 関連補題を再利用する。

**難度**: ★★☆☆☆（既存証明依存関係に注意）

**効果（中）**:
- `sortFallingUnits_perm` を `List.mergeSort_perm` で置換可能
- `insertSorted_perm` 等の補題が削減できる

**障害**:
- Mathlib の `List.Sorted`/`List.mergeSort` は `Preorder`/`TotalOrder` を要求
- `shouldProcessBefore` は全順序でない（tied ペアで tie-break 値依存）
- 既存の `insertSorted_split`（位置分解）等の証明が依存関係を持つ

**推奨**: 全面置換より、`List.Perm` 関連補題（`List.perm_merge` 等）の個別活用にとどめる。

---

### B-3. `FallingUnit.positions` の Finset 化 — **現状維持推奨**

**概要**: `FallingUnit.positions` を `List QuarterPos` から `Finset QuarterPos` に変更し、位置素性を `Finset.Disjoint` で表現する。

**棄却理由**:
- `placeFallingUnit` の実装が `foldl f positions` に依存（順序が必要）
- `Finset` は順序を持たないため `foldl` が定義できない
- 現在の `placeFallingUnit_ext`（`.any 等価 → foldl 等価`）パターンは既に機能している

**部分活用**: メンバーシップ判定のみ Finset で表現し、実装は `List` のまま維持する二重管理は現実的。

---

### B-4. `omega` タクティクの積極活用 ← **適用済み（2026-03-31）**

**概要**: 自然数算術に関する手動証明を `omega` で置換する。

**難度**: ★☆☆☆☆

**適用結果**:

| 項目 | 値 |
|---|---|
| 適用ファイル数 | 3 (`Gravity.lean`, `GenericBfs.lean`, `CrystalBond.lean`) |
| 置換箇所数 | 16 箇所 |
| ビルド結果 | errors: 0 / sorries: 2 / warnings: 18（変更前と同等） |

**置換カテゴリと件数**:

| カテゴリ | 件数 | 例 |
|---|---|---|
| `Nat.le_refl _` → `by omega` / `simp` | 3 | `placeQuarter_length`, `h_mono` |
| `Nat.zero_le _` → `by omega` | 5 | `insertSorted_split` 全ケース |
| `Nat.pos_of_ne_zero (by omega)` → `by omega` | 3 | `structuralClusterList` 内 |
| `Nat.pos_of_ne_zero h` → `by omega` | 1 | `invCount > 0` の導出 |
| `Nat.le_of_lt h` → `by omega` | 2 | `add_sq_le_sq_of_lt` (GenericBfs, CrystalBond) |
| `Nat.le_trans hd h` → `by omega` | 1 | `minLayer_le_layer` |
| `Nat.le_antisymm (by omega) h` → `by omega` | 1 | `tied_no_shared_dir` 内 `lu = lv` |
| `Nat.mul_pos` のネスト簡略化 | 1 | `structuralClusterList_complete` |
| `h_lc_pos` + `h_n_pos` の中間段階統合 | 1 | `allStructuralClustersList` 内 |

**omega 適用不可だったパターン**:

| パターン | 理由 |
|---|---|
| `Nat.le_trans (lemma_result) (Nat.min_le_left ...)` | 再帰補題の結果を omega が推論できない |
| `Nat.mul_le_mul h1 h2`（変数×変数） | 非線形算術は omega の守備範囲外 |
| `Nat.mul_pos (by omega) (by omega)`（最外） | `n * n > 0` は非線形 |
| `foldMinOption` 関連の `Nat.le_trans` | foldl/min の関数結果に依存 |

**効果**: 手動の `Nat.*` 呼び出しが減り、算術証明の意図が明確化。
今後新しい証明を書く際は **`omega` を第一選択** とし、失敗時のみ `Nat.*` に頼る方針を推奨。

詳細は [`docs/knowledge/lean-proof-tips.md`](knowledge/lean-proof-tips.md) の `omega` セクションを参照。

---

## 優先度サマリー

| 優先度 | アプローチ | 効果 | 備考 |
|---|---|---|---|
| **最高** | A-1: `floatingUnits_spb_rank` | sorry 解消の前提 | 幾何制約形式化が難所 |
| **高** | A-2: `sortFU_foldl_perm_input_eq` | 残 sorry 全解消 | A-1 完成で直線的に進む |
| **中** | B-4: `omega` 積極活用 | 既存証明の簡略化 | **適用済み**（16箇所） |
| **低** | B-2: mergeSort 部分統合 | Perm 補題の削減 | 移行コスト高 |
| **棄却** | B-1: SimpleGraph 統合 | — | Fintype 制約で利用不可 |
| **棄却** | B-3: positions Finset 化 | — | placeFallingUnit が List 前提 |

---

## 参考: 利用可能な主要証明インフラ

A-1/A-2 の証明で直接使える既存補題:

| 補題 | 用途 |
|---|---|
| `allStructuralClusters_disjoint` | 異クラスタ位置素性（幾何制約の基盤） |
| `structuralClusterList_sound` / `_complete` | BFS 到達可能性の健全性・完全性 |
| `floatingUnits_pairwise_disjoint` | 浮遊単位間の位置素性 |
| `floatingUnits_nodup` | NoDup 性 |
| `insertSorted_split` | 挿入位置の分解（take k ++ [u] ++ drop k） |
| `tied_no_shared_dir` | tied ペア → 方角列非共有 |
| `foldl_eq_of_perm_tied_adj_comm` | tied 隣接ペアの swap で foldl 不変 |
| `settleStep_comm_ne_dir` | 方角列素ペアの settle 可換性 |
