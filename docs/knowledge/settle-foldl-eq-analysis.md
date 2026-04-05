# settle_foldl_eq 証明の分析と教訓

> **注意**: 本文中の行番号は 2026-03-31 時点のものであり、その後のリファクタリング
> （半シェイプ関連コードの削除等）により実際の行番号とは異なる可能性がある。
> 戦略的知見は引き続き有効。

`Gravity.lean` の最後の sorry である `settle_foldl_eq` の証明過程で得られた知見。

---

## 問題の概要

`settle_foldl_eq` は以下を主張する:

```lean
Shape.ofLayers
  ((sortFallingUnits ((floatingUnits s).map FallingUnit.rotate180)).foldl
    (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs) =
Shape.ofLayers
  ((sortFallingUnits (floatingUnits s.rotate180)).foldl
    (fun obs u => placeFallingUnit s.rotate180 obs u (landingDistance u obs)) obs)
```

LHS は `(floatingUnits s).map r180` をソートして foldl し、
RHS は `floatingUnits s.r180` をソートして foldl する。
両者の入力リストは BFS 順序の違いにより **リストとして等しくない**。

---

## 難航した点と得られた知見

### 1. 偽定理パターンの早期発見が遅れた

**問題**: 過去のセッションで「flatMap .any 等価 + 位置素 → foldl 結果一致」という
偽命題をベースに証明を構築し、大量のコードが無駄になった。

**教訓**: 命題を Lean コードにする前に、具体的な反例を手計算で確認すべき。
特に `foldl` の順序依存性がある場合、入力の分割方法（グルーピング）が結果に影響するため、
「位置集合が同じ ≠ ユニット分割が同じ」であることに注意する。

### 2. shouldProcessBefore (shouldProcessBefore) の非反対称性

**問題**: `shouldProcessBefore` は一般には反対称律を満たさない（循環ペアが存在する）。
しかし、`floatingUnits` の構造クラスタ同士に限れば位置素性と接続性により反対称が成立する。

**発見**: 一般の `FallingUnit` ペアでは循環ペアが構成可能:
```
A = {(layer 0, NE), (layer 3, SW)}, B = {(layer 1, NE), (layer 2, SW)}
→ shouldProcessBefore(A,B) = true (NE列: 0<1), shouldProcessBefore(B,A) = true (SW列: 2<3)
```
ただし、これらは **構造クラスタとして接続するためのパスが中間層を通過** し、
**異なるクラスタは同レイヤ隣接方角に同時に存在できない** ため、
`floatingUnits` 上では矛盾に帰着される。

### 3. 「接続性 → 中間層の占有」という幾何的制約の形式化が困難

**問題**: cluster-cluster の反対称性は以下の幾何的事実に依存する:

1. **同レイヤ隣接方角排除**: 異なる構造クラスタは同一レイヤの隣接方角に位置を持てない（もし持てば構造結合により同一クラスタになるため）。
2. **4方角の環状構造**: {NE, SE, SW, NW} は環状に隣接（NE-SE-SW-NW-NE）。非隣接ペアは対角（NE↔SW, SE↔NW）のみ。
3. **方角遷移層の排他性**: クラスタが水平結合（同レイヤ隣接方角）で方角を変える層では、そのクラスタが 2 方角を占有するため、他のクラスタはその層に一切位置を持てない。

これらの事実を組み合わせた「パスの中間値定理」的議論が必要だが、
List ベースの BFS 定義上で形式化するのは非常に手間がかかる。

**具体的な困難**:
- `structuralCluster` は BFS で構築されるため、パスの構造を直接参照しにくい
- `GenericReachable` は存在命題（到達可能性）だが、パスの各要素の性質（方角・レイヤ）を抽出するには帰納法でパスを分解する必要がある
- 4 方角 × 複数レイヤの場合分けが膨大

### 4. 証明戦略の堂々巡り

**問題**: 以下の戦略候補を繰り返し検討し、コードを書いては破棄する循環に陥った:

| 戦略 | 棄却理由 |
|---|---|
| リスト等号 `fU s.r180 = (fU s).map r180` | BFS 順序差で偽 |
| flatMap .any 等価 + 位置素 → foldl 一致 | ユニット分割差で偽 |
| pointwise .any equiv → foldl 一致 | 入力順序が異なり pointwise にならない |
| multiset .any equiv → sort 後 pointwise | tied ペアの順序が入力順依存 |
| shouldProcessBefore 反対称律 → tied swap 不変 → foldl 一致 | 反対称律の cluster-cluster 証明が困難 |
| h_x_trans 除去によるリファクタ | DISPROVEN (1400行の作業が無駄に) |

**教訓**: 戦略レベルの判断をコード着手前に確定させる仕組みが必要。
探索的にコードを書き始めると、sunk cost バイアスで損切りが遅れる。

### 5. QuarterPos.rotate180 はレイヤを変えない

**発見**: `QuarterPos.rotate180` は方角のみ回転し、レイヤは変えない:
```lean
def rotate180 (p : QuarterPos) : QuarterPos :=
    { layer := p.layer, dir := p.dir.rotate180 }
```
`Shape.rotate180` も `mapLayers Layer.rotate180`（レイヤ順序は不変）。
これにより r180 は `minLayerAtDir` を方角間で移動させる:
- `p.minLayerAtDir d` under r180 → `p.minLayerAtDir d.r180`

---

## 現在の状態 (2026-03-25 第2セッション更新)

### ⚠️ 重大発見 (第1セッション): `sortFU_preserves_spb_order` は偽定理

**2026-03-25 第1セッションで発見・削除済み**。
仮定 `shouldProcessBefore(a,b)=true, shouldProcessBefore(b,a)=false` はペアワイズな 2-cycle 禁止しか保証せず、
第三者との **3-cycle** が insertSorted のグリーディ動作を破壊する。

#### 反例

```
a = cluster [⟨0, .ne⟩, ⟨5, .se⟩]
b = cluster [⟨3, .ne⟩, ⟨0, .sw⟩]
w = cluster [⟨3, .sw⟩, ⟨0, .se⟩]

shouldProcessBefore: a→b (ne:0<3), b→w (sw:0<3), w→a (se:0<5)  ← 3-cycle
全ペア 2-cycle なし → DAG でないと破綻
l = [w, a, b] → sortFallingUnits = [b, w, a] → 定理に矛盾
```

### ⚠️ 重大発見 (第2セッション): `sortFallingUnits_foldl_perm_input_eq` 一般版は偽

**2026-03-25 第2セッションで発見**。旧版（h_disj + h_rank 仮定）は一般入力で偽。
→ floatingUnits 限定版 (h_sub) に修正済み。詳細は「証明計画」セクションを参照。

### ⚠️ 重大発見 (第2セッション): tiebreaker 辞書式全順序化は不可能

r180 が方角を置換するため、辞書式全順序は r180 非等変。
→ tiebreaker 修正アプローチを全面棄却。

### 旧発見: `spb_antisymm_of_disjoint` は偽

前セッションで発見済み。位置素のみでは反対称律不成立。

### コード構造 (2026-04-05 第5セッション更新)

ファイル: `Gravity.lean` (~6,500行、sorry 1件)

1. **l_mid 構築**: Classical choice で `g : fU(s) → fU(s.r180)` を構築。✅ 証明済
2. **Step 2**: `sortFallingUnits l1 foldl = sortFallingUnits l_mid foldl` — `sorted_foldl_pointwise_eq` で ✅ 証明済
3. **Step 3**: `sortFallingUnits l_mid foldl = sortFallingUnits l2 foldl` — `sortFallingUnits_foldl_perm_input_eq` で ✅ 証明済 (S-5 sorry 内包)

### 残 sorry (1 個) — 2026-04-05 第5セッション更新

| 定理 | 行 | 状態 | 依存関係 |
|---|---|---|---|
| `shouldProcessBefore_no_chain` | L5605 | ❌ **FALSE** | `foldl_insertSorted_preserves_spb_order` Case 3 |

**証明チェーン（下流は全て不健全）**:
```
shouldProcessBefore_no_chain (sorry, FALSE)
  → foldl_insertSorted_preserves_spb_order (Case 3 が不健全)
    → sortFallingUnits_spb_order_preserving (一般入力で偽)
      → sortFallingUnits_inversion_is_tied (一般 Perm で偽)
        → sortFallingUnits_inversion_dir_disjoint
          → sortFallingUnits_foldl_perm_input_eq
            → settle_foldl_eq
              → process_rotate180
```

**解消済み**:
- `shouldProcessBefore_no_mutual` (S-1): ✅ 完了 — d1≠d2 の 4-horizontal-step 矛盾戦略で証明
- `insertSorted_preserves_relative_order` (S-2): ✅ 完了 — insertSorted_split + 3 ケース分岐
- `sortFU_spb_one_way_order` (S-3): ❌ **偽と判明、削除済み** — fU 上でも shouldProcessBefore 非推移性で反例
- `floatingUnits_spb_rank`: ❌ **不要化・削除済み** — バブルソート帰納法に切り替え
- `sortFallingUnits_foldl_perm_input_eq`: ✅ 完了 — `foldl_eq_of_perm_tied_adj_comm` + S-4 で証明
- `sortFallingUnits_inversion_is_tied` (S-4a): ✅ 完了 — shouldProcessBefore_no_chain(sorry) 経由
- `sortFallingUnits_inversion_dir_disjoint` (S-4b): ✅ 完了 — S-4a 経由
- `shouldProcessBefore_no_chain` (S-5): ❌ **偽と判明** — 同列 3 ピンで反例

### 削除した偽定理

| 定理 | 理由 |
|---|---|
| `spb_antisymm_of_disjoint` | 位置素のみでは反対称律不成立 (反例あり) |
| `foldl_sorted_disjoint_flatMap_eq` | flatMap .any 等価 + 位置素では unit 分割不一致 |
| `sortFU_preserves_spb_order` | 3-cycle 下で insertSorted の順序保存が偽 (第1セッション) |
| `floatingUnits_spb_no_cycle` | DAG rank 版に置き換え後、全面削除 |
| `sortFallingUnits_foldl_perm_input_eq` (一般版) | h_disj+h_rank 仮定では偽 → fU 限定版に修正 (第2セッション) |
| `sortFU_spb_one_way_order` | fU 上でも shouldProcessBefore 非推移性で偽 (第3セッション) |
| `sortFU_spb_order_on_fU` | 同根 (第3セッション) |
| `floatingUnits_spb_rank` | バブルソート帰納法に切り替え、不要化 (第3セッション) |
| `shouldProcessBefore_no_chain` | 同列 3+ ピンで反例 (第5セッション)、**要削除** |

### ⚠️ 要削除/修正の定理 (shouldProcessBefore_no_chain 波及)

| 定理 | 状態 | 修正方針 |
|---|---|---|
| `shouldProcessBefore_no_chain` | FALSE、要削除 | 代替不要（下流を直接修正） |
| `foldl_insertSorted_preserves_spb_order` | Case 3 不健全 | r180 特化版に置き換え or 削除 |
| `sortFallingUnits_spb_order_preserving` | 一般入力で偽 | r180 特化版に置き換え or 削除 |
| `sortFallingUnits_inversion_is_tied` | 一般 Perm で偽 | r180 特化版に置き換え or 削除 |

---

## 証明計画 (2026-04-05 第5セッション改訂)

### 現在の構造（不健全チェーン）

```
settle_foldl_eq
  ├─ l_mid 構築 (Classical choice)                    ✅ 証明済
  ├─ Step 2: sorted_foldl_pointwise_eq               ✅ 証明済
  └─ Step 3: sortFallingUnits_foldl_perm_input_eq (fU限定)     ✅ 証明済 (不健全チェーン内包)
       └─ foldl_eq_of_perm_tied_adj_comm              ✅ 証明済
            └─ sortFallingUnits_inversion_dir_disjoint          ✅ 証明済 (不健全)
                 └─ sortFallingUnits_inversion_is_tied          ✅ 証明済 (不健全)
                      └─ sortFallingUnits_spb_order_preserving ✅ 証明済 (不健全)
                           └─ foldl_insertSorted_preserves_spb_order (不健全)
                                └─ shouldProcessBefore_no_chain       ← sorry (FALSE)
```

### 第5セッションでの重大発見 (2026-04-05)

**`shouldProcessBefore_no_chain` (S-5) は FALSE**。同列 3 ピン・混合方角チェーンで反例あり。
詳細は [`gravity-equivariance-analysis.md`](gravity-equivariance-analysis.md) 参照。

影響:
- `foldl_insertSorted_preserves_spb_order` Case 3: shouldProcessBefore_no_chain 直接使用 → 不健全
- `sortFallingUnits_spb_order_preserving`: 一般入力で偽
- `sortFallingUnits_inversion_is_tied`: 一般 Perm で偽（第4セッション既知）
- **`process_rotate180` 自体は TRUE**（l_mid/l2 ペアでは 0 violations）

### 修正計画

#### 基本方針: 不健全チェーン（4定理）を廃止し、r180 固有構造で直接証明

削除対象: `shouldProcessBefore_no_chain`, `foldl_insertSorted_preserves_spb_order`,
`sortFallingUnits_spb_order_preserving`, `sortFallingUnits_inversion_is_tied`

#### 証明ルート候補

**ルート α（推奨）: sortFallingUnits_inversion_dir_disjoint に r180 仮説を追加**

追加仮説: `h_input_tied : ∀ a b, 入力反転 → tied(a, b) ∧ direction-disjoint(a, b)`

r180 由来の入力反転は同レイヤ・反対方角ペアのみ（計算確認済み）。
幾何制約（クラスタの方角遷移層封鎖）により tied swap が他要素の insertSorted 挙動を変えない。

改修スコープ: sortFallingUnits_inversion_dir_disjoint + sortFallingUnits_foldl_perm_input_eq + settle_foldl_eq

**ルート β: settle_foldl_eq Phase 2 を書き直し**

sortFallingUnits_foldl_perm_input_eq を使わず、settle_foldl_eq 内で直接
foldl_eq_of_perm_tied_adj_comm を呼び、h_tied_comm を inline で証明。

利点: 中間定理のシグネチャ変更が最小。
欠点: settle_foldl_eq が大幅に膨張。

#### 注意: h_input_tied だけでは不十分

一般の h_input_tied（入力反転が tied）では出力反転も tied とは限らない。
反例: cluster({(2,SW),(6,NE)}) + pin(4,NE) + pin(4,SW) パターン。
ただしこの反例は floatingUnits の幾何制約（クラスタが方角遷移層を封鎖し、
同層の他ユニット位置を排除）で排除される。幾何制約の形式証明が核心。

---

### 過去の発見（第4セッション）

**重大発見**: `sortFallingUnits_inversion_is_tied` の現型シグネチャは **一般の l1.Perm l2 に対して FALSE**。
3L 3色、fU 要素 ≤ 4 の全順列テストで 8628 violations（Scratch/AllPermInvCheck.lean）。

**h_ow 条件** (shouldProcessBefore(a,b)=true → a before b in both inputs) では **0 violations**。

**l_mid/l2 ペアでは 0 violations** (SortedInvTiedCheck.lean で確認):
- 入力反転は同レイヤ・別方角ペアのみ（r180 方角回転で allValid 順序が変わる）
- これらは必ず tied（方角非共有 → shouldProcessBefore 双方 false）
- sortFallingUnits の insertSorted 補正が両入力で同一のパターンで行われるため出力も tied のみ

### 過去の発見（第3セッション）

1. **S-1 `shouldProcessBefore_no_mutual` 完了**: d1≠d2 の 4-horizontal-step 矛盾戦略で証明
2. **S-2 `insertSorted_preserves_relative_order` 完了**: insertSorted_split + 3 case 分岐
3. **S-3 `sortFU_spb_one_way_order` は偽と判明**: fU 上の shouldProcessBefore 非推移性 → 削除
4. **S-4b `sortFallingUnits_inversion_dir_disjoint` 完了**: tied + position-disjoint → direction-disjoint
5. **`sortFallingUnits_foldl_perm_input_eq` 本体完成**: `foldl_eq_of_perm_tied_adj_comm` + S-4b

**棄却済み**:
- DAG rank ベース（floatingUnits_spb_rank）→ shouldProcessBefore は DAG でない場合あり
- sortFallingUnits shouldProcessBefore 順序保存（S-3）→ shouldProcessBefore 非推移性で偽
- tiebreaker 辞書式全順序化 → r180 非等変

---

## 既存インフラの使用可否サマリー (2026-04-04 第3セッション更新)

| 補題 | 状態 | 用途 |
|---|---|---|
| `insertSorted_split` | ✅ 証明済 | insertSorted は take k ++ [u] ++ drop k 形式で分解可能 |
| `shouldProcessBefore_no_mutual` | ✅ 証明済 | floatingUnits 間で shouldProcessBefore 双方向 true 不可 |
| `insertSorted_preserves_relative_order` | ✅ 証明済 | insertSorted が既存要素の相対順序保存 |
| `sortFallingUnits_inversion_dir_disjoint` | **sorry** | sortFallingUnits の反転ペアが direction-disjoint |
| `sortFallingUnits_foldl_perm_input_eq` | ✅ 証明済 | fU 限定: Perm 入力 → foldl 一致 (S-4 に依存) |
| `sortFallingUnits_rotate180` | ✅ 証明済 | LHS の map r180 を sortFallingUnits 内部に移動 |
| `shouldProcessBefore_ext` | ✅ 証明済 | shouldProcessBefore は .any にのみ依存 |
| `tied_no_shared_dir` | ✅ 証明済 | tied ペア → 方角素 |
| `foldl_eq_of_perm_tied_adj_comm` | ✅ 証明済 | bubble sort 帰納: Perm + dir-disjoint 反転 → foldl 一致 |
| `foldl_settle_head_swap` | ✅ 証明済 | 方角素隣接要素の swap → foldl 不変 |
| `foldl_settle_swap_at` | ✅ 証明済 | prefix 付き方角素 swap → foldl 不変 |
| `settleStep_comm_ne_dir` | ✅ 証明済 | 方角素ペアの settleStep 可換 |
| `foldl_pointwise_ext` | ✅ 証明済 | pointwise .any equiv → foldl 一致 |
| `sorted_foldl_pointwise_eq` | ✅ 証明済 | pointwise .any equiv 入力 → sortFallingUnits foldl 一致 |
| `floatingUnits_pairwise_disjoint` | ✅ 証明済 | floatingUnits の位置素性 |
| `floatingUnits_nodup` | ✅ 証明済 | NoDup 性 |
| `sortFallingUnits_perm` | ✅ 証明済 | sortFallingUnits は入力の置換 |
| `floatingUnits_length_rotate180` | ✅ 証明済 | \|fU(s)\| = \|fU(s.r180)\| |
| `floatingUnit_any_in_rotate180` | ✅ 証明済 | 各 u ∈ fU(s) に .any 等価な v ∈ fU(s.r180) |
| `map_rotate180_pairwise_disjoint` | ✅ 証明済 | 位置素性は map r180 で保存 |
| `invCount_adj_swap_lt` | ✅ 証明済 | 隣接反転 swap で転置数が減少 |
