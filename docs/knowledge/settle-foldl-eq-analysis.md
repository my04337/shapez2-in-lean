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

### 2. spb (shouldProcessBefore) の非反対称性

**問題**: `shouldProcessBefore` は一般には反対称律を満たさない（循環ペアが存在する）。
しかし、`floatingUnits` の構造クラスタ同士に限れば位置素性と接続性により反対称が成立する。

**発見**: 一般の `FallingUnit` ペアでは循環ペアが構成可能:
```
A = {(layer 0, NE), (layer 3, SW)}, B = {(layer 1, NE), (layer 2, SW)}
→ spb(A,B) = true (NE列: 0<1), spb(B,A) = true (SW列: 2<3)
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
| spb 反対称律 → tied swap 不変 → foldl 一致 | 反対称律の cluster-cluster 証明が困難 |
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

## 現在の状態 (2026-06 第2セッション更新)

### ⚠️ 重大発見 (第1セッション): `sortFU_preserves_spb_order` は偽定理

**2026-06 第1セッションで発見・削除済み**。
仮定 `spb(a,b)=true, spb(b,a)=false` はペアワイズな 2-cycle 禁止しか保証せず、
第三者との **3-cycle** が insertSorted のグリーディ動作を破壊する。

#### 反例

```
a = cluster [⟨0, .ne⟩, ⟨5, .se⟩]
b = cluster [⟨3, .ne⟩, ⟨0, .sw⟩]
w = cluster [⟨3, .sw⟩, ⟨0, .se⟩]

spb: a→b (ne:0<3), b→w (sw:0<3), w→a (se:0<5)  ← 3-cycle
全ペア 2-cycle なし → DAG でないと破綻
l = [w, a, b] → sortFU = [b, w, a] → 定理に矛盾
```

### ⚠️ 重大発見 (第2セッション): `sortFU_foldl_perm_input_eq` 一般版は偽

**2026-06 第2セッションで発見**。旧版（h_disj + h_rank 仮定）は一般入力で偽。
→ floatingUnits 限定版 (h_sub) に修正済み。詳細は「証明計画」セクションを参照。

### ⚠️ 重大発見 (第2セッション): tiebreaker 辞書式全順序化は不可能

r180 が方角を置換するため、辞書式全順序は r180 非等変。
→ tiebreaker 修正アプローチを全面棄却。

### 旧発見: `spb_antisymm_of_disjoint` は偽

前セッションで発見済み。位置素のみでは反対称律不成立。

### コード構造 (2026-06 第2セッション時点)

ファイル: `Gravity.lean` (~5710行、sorry 2件)

1. **l_mid 構築**: Classical choice で `g : fU(s) → fU(s.r180)` を構築。✅ 証明済
2. **Step 2**: `sortFU l1 foldl = sortFU l_mid foldl` — `sorted_foldl_pointwise_eq` で ✅ 証明済
3. **Step 3**: `sortFU l_mid foldl = sortFU l2 foldl` — `sortFU_foldl_perm_input_eq` (fU限定版) で依存

### 残 sorry (2 個)

| 定理 | 行 | 状態 | 依存関係 |
|---|---|---|---|
| `floatingUnits_spb_rank` | L5556 | sorry | fU 上の spb DAG → rank 関数存在 |
| `sortFU_foldl_perm_input_eq` | L5585 | sorry (TRUE) | fU 限定 Perm → foldl 一致 |

### 削除した偽定理

| 定理 | 理由 |
|---|---|
| `spb_antisymm_of_disjoint` | 位置素のみでは反対称律不成立 (反例あり) |
| `foldl_sorted_disjoint_flatMap_eq` | flatMap .any 等価 + 位置素では unit 分割不一致 |
| `sortFU_preserves_spb_order` | 3-cycle 下で insertSorted の順序保存が偽 (第1セッション) |
| `floatingUnits_spb_no_cycle` | DAG rank 版 (`floatingUnits_spb_rank`) に置き換え |
| `sortFU_foldl_perm_input_eq` (一般版) | h_disj+h_rank 仮定では偽 → fU 限定版に修正 (第2セッション) |

---

## 証明計画 (2026-06 第2セッション改訂)

### 現在の構造

```
settle_foldl_eq
  ├─ l_mid 構築 (Classical choice)                    ✅ 証明済
  ├─ Step 2: sorted_foldl_pointwise_eq               ✅ 証明済
  └─ Step 3: sortFU_foldl_perm_input_eq (fU限定)     ← sorry
```

### ⚠️ 重大発見 (第2セッション): `sortFU_foldl_perm_input_eq` 一般版は偽

**2026-06 第2セッションで発見**: 旧版 `sortFU_foldl_perm_input_eq`
(仮定: h_disj + h_rank) は一般入力で **偽**。

#### 反例

```
x = pin(NE, 7), u = cluster[(NE,8),(SW,1)], w = pin(SW, 3)
DAG: rank(x)=0 < rank(u)=1 < rank(w)=2
spb(x,u)=true, spb(u,w)=true, x と w は tied (方角素)

l1 = [w, x, u] → sortFU = [u, w, x]
l2 = [x, u, w] → sortFU = [w, x, u]
→ u が w,x 両方と方角共有 → foldl 不可換 → 結果が異なる
```

全仮定 (Perm, NoDup, 位置素, DAG ランク) を満たすが結論は偽。

#### 原因

insertSorted が u を挿入する際、spb(u,w)=true で w の前に停止。
tied な x は w より後（tiebreaker 順）なので、u は x より前に配置される。
結果: spb(x,u)=true なのに u が x より前 → 非 tied 反転ペア → foldl 不可換。

#### 修正

定理文を floatingUnits 限定に変更:
```lean
(h_sub : ∀ x, x ∈ l1 → x ∈ floatingUnits s)
```
floatingUnits の幾何制約（方角遷移層の排他性）により反例パターンは排除される。

### 棄却: tiebreaker 辞書式全順序化

r180 が方角を置換 (NE↔SW, SE↔NW) するため、
方角の固定順序に基づく辞書式比較は r180 非等変。
u ≠ u.r180 のペアでは比較結果が r180 で反転し、
`sortFallingUnits_rotate180` が壊れる。

### 修正の選択肢（更新版）

詳細は `docs/plans/gravity-rotate180-proof-plan.md` §7 を参照。

- **Phase 1**: `floatingUnits_spb_rank` の証明 (幾何制約 → DAG)
- **Phase 2**: `sortFU_foldl_perm_input_eq` の証明
  - 方法A: sortFU 反転ペアが全て direction-disjoint を証明
  - 方法B: floatingUnits 上の sortFU が入力順序非依存を直接証明
  - 方法C: rankSort を定義して sortFU foldl = rankSort foldl を tied 可換で証明

---

## 既存インフラの使用可否サマリー

| 補題 | 状態 | 位置 | 用途 |
|---|---|---|---|
| `insertSorted_split` | ✅ 証明済 | L4334 | insertSorted は take k ++ [u] ++ drop k 形式で分解可能 |
| `floatingUnits_spb_rank` | sorry | L5556 | floatingUnits 上の spb DAG → rank 関数存在 |
| `sortFU_foldl_perm_input_eq` | sorry | L5585 | fU 限定: Perm 入力 → foldl 一致 |
| `sortFallingUnits_rotate180` | ✅ 証明済 | L694 | LHS の map r180 を sortFU 内部に移動 |
| `shouldProcessBefore_ext` | ✅ 証明済 | | spb は .any にのみ依存 |
| `tied_no_shared_dir` | ✅ 証明済 | | tied ペア → 方角素 |
| `foldl_eq_of_perm_tied_adj_comm` | ✅ 証明済 | L5228 | bubble sort 帰納: Perm + dir-disjoint 反転 → foldl 一致 |
| `foldl_settle_head_swap` | ✅ 証明済 | | 方角素隣接要素の swap → foldl 不変 |
| `foldl_settle_swap_at` | ✅ 証明済 | | prefix 付き方角素 swap → foldl 不変 |
| `settleStep_comm_ne_dir` | ✅ 証明済 | | 方角素ペアの settleStep 可換 |
| `foldl_pointwise_ext` | ✅ 証明済 | | pointwise .any equiv → foldl 一致 |
| `sorted_foldl_pointwise_eq` | ✅ 証明済 | | pointwise .any equiv 入力 → sortFU foldl 一致 |
| `floatingUnits_pairwise_disjoint` | ✅ 証明済 | | floatingUnits の位置素性 |
| `floatingUnits_nodup` | ✅ 証明済 | | NoDup 性 |
| `sortFallingUnits_perm` | ✅ 証明済 | L844 | sortFU は入力の置換 |
| `floatingUnits_length_rotate180` | ✅ 証明済 | | \|fU(s)\| = \|fU(s.r180)\| |
| `floatingUnit_any_in_rotate180` | ✅ 証明済 | | 各 u ∈ fU(s) に .any 等価な v ∈ fU(s.r180) |
| `map_rotate180_pairwise_disjoint` | ✅ 証明済 | | 位置素性は map r180 で保存 |
| `invCount_adj_swap_lt` | ✅ 証明済 | | 隣接反転 swap で転置数が減少 |
