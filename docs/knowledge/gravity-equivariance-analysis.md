# Gravity 180° 回転等変性 証明の知見

`Gravity.lean` における `process_rotate180`（180° 回転等変性）の証明で得られた
Gravity 固有の知見。汎用的な Lean 4 の Tips は [`lean-proof-tips.md`](lean-proof-tips.md) を参照。

---

## `shouldProcessBefore` は反対称律を満たさない

`shouldProcessBefore` は各方角列での最小レイヤの大小比較であり、**循環ペアが存在する**。

```
例: クラスタ A = {(layer 0, East), (layer 3, West)}
    クラスタ B = {(layer 1, East), (layer 2, West)}
  → East 列: minLayer A=0 < minLayer B=1 → shouldProcessBefore A B = true
  → West 列: minLayer B=2 < minLayer A=3 → shouldProcessBefore B A = true
```

したがって「shouldProcessBefore は DAG」という主張は **偽** である。
決定性の証明は、循環ペアが方角列ごとに異なる上下関係を持つことを利用し、
`settleStep_comm_ne_dir`（異なる方角列での settleStep の交換法則）で示す必要がある。

---

## `sortFU_preserves_spb_order` は偽定理

仮定は **2 要素間のペアワイズな非循環** (`shouldProcessBefore(b,a)=false`) しか要求しないが、
第三者 `w` との 3-cycle が `insertSorted` のグリーディ挿入を狂わせる。

```
a = cluster [⟨0, .ne⟩, ⟨5, .se⟩]
b = cluster [⟨3, .ne⟩, ⟨0, .sw⟩]
w = cluster [⟨3, .sw⟩, ⟨0, .se⟩]

shouldProcessBefore 関係: a→b (ne:0<3), b→w (sw:0<3), w→a (se:0<5)  ← 3-cycle
各ペアは 2-cycle なし (仮定を満たす):
  shouldProcessBefore(a,b)=true, shouldProcessBefore(b,a)=false ✓  shouldProcessBefore(b,w)=true, shouldProcessBefore(w,b)=false ✓  shouldProcessBefore(w,a)=true, shouldProcessBefore(a,w)=false ✓
```

`l = [w, a, b]` での `sortFallingUnits` の動作で b が a より前に来てしまい、
`a の position > b の position` となって定理に矛盾する。

### 教訓

1. **ペアワイズ非循環 ≠ DAG**: 全ペアの 2-cycle がなくても 3-cycle 以上が存在しうる
2. **修正方針**: `h_no_cycle` を 2-cycle 禁止から **DAG 条件** に強化するか、
   証明構造を根本的に見直す必要がある

詳細な分析は [`settle-foldl-eq-analysis.md`](settle-foldl-eq-analysis.md) を参照。

---

## `shouldProcessBefore_no_chain` (S-5) は偽定理（2026-04-05 第5セッションで発見）

「floatingUnits の要素間で shouldProcessBefore の連鎖 (a→b→c) は生じない」は **FALSE**。

### 反例 1: 同列 3 ピン（6 層）

```
Shape: "--------:P-------:--------:P-------:--------:P-------"
floatingUnits: [pin(1,NE), pin(3,NE), pin(5,NE)]
shouldProcessBefore(pin1→pin3) = true (NE: 1<3)
shouldProcessBefore(pin3→pin5) = true (NE: 3<5) → CHAIN
```

### 反例 2: 混合方角（4 層）

```
Shape: "--------:P-------:CrCr----:--P-----"
floatingUnits: [cluster({SE@2,NE@2}), pin(1,NE), pin(3,SE)]
shouldProcessBefore(pin(1,NE)→cluster) = true (NE: 1<2)
shouldProcessBefore(cluster→pin(3,SE)) = true (SE: 2<3) → CHAIN
```

### 根本原因

- pin は `canFormBond = false` → 構造結合不可能 → 常に独立 floatingUnit
- 同一方角列内に複数の独立ピンが存在可能（layer 0 が空の場合）
- 事前の計算検証が 2L/3L 小規模シェイプのみで 4L+ を未検証だった

### 波及範囲

`shouldProcessBefore_no_chain` に依存する以下の補題チェーンが全て不健全:

1. `foldl_insertSorted_preserves_spb_order` — Case 3 が不健全
2. `sortFallingUnits_spb_order_preserving` — 一般の入力順で偽
3. `sortFallingUnits_inversion_is_tied` — 一般の Perm で偽
4. `sortFallingUnits_inversion_dir_disjoint` — `is_tied` 経由で依存

**ただし `process_rotate180` 自体は TRUE**（全反例シェイプで計算検証済み）。

### 修正方針

証明チェーンの中間補題は「一般の Perm に対して」は偽だが、
r180 由来の **特定の Perm に対しては TRUE**（計算で確認済み）。

修正候補:
- **A**: `sortFallingUnits_inversion_dir_disjoint` を r180 固有構造で直接証明（推奨）
- **B**: 中間補題に h_input_tied 仮説を追加してシグネチャ特殊化
- **C**: settle_foldl_eq Phase 2 全体を書き直し

詳細は [`settle-foldl-eq-analysis.md`](settle-foldl-eq-analysis.md) を参照。

---

## `insertSorted` のグリーディ挿入の動作特性

`insertSorted u sorted fuel`:
1. sorted を先頭から順にスキャンする
2. `shouldProcessBefore(u, v) = true` → v の前に u を挿入して停止
3. `shouldProcessBefore(v, u) = true` → v をスキップして次へ
4. tied (shouldProcessBefore 双方 false): tiebreaker 比較 (`tb u ≤ tb v` なら u を前に挿入)
5. リスト末尾到達 → 末尾に u を追加

**重要な性質**:
- `insertSorted_split`: 結果は `sorted.take k ++ [u] ++ sorted.drop k` の形 ✅ 証明済
- `insertSorted` は **最初のマッチで停止** する → 3-cycle があると期待位置に到達しない
- `insertSorted` による相対順序保存は、sorted リストの既存要素間では成立する
  （新要素 u の挿入位置のみが変わり、既存要素の相対順序は維持される）

---

## `any_pred_ext` パターン — `.any (· == p)` から `.any f` への橋渡し

2 つのリストが要素の存在性（`.any (· == p)`）で同値であることから、
任意の述語 `f` についても `.any f` が同値であることを示すパターン。

**原理**: `.any (· == p)` の同値性はリストが同じ「マルチ集合」であることを意味し、
任意の述語に対する `.any f` も保存される。

```lean
private theorem any_pred_ext {l1 l2 : List QuarterPos}
        (h : ∀ p, l1.any (· == p) = l2.any (· == p))
        (f : QuarterPos → Bool) :
        l1.any f = l2.any f
```

---

## BFS リスト等号は偽命題パターン（再確認）

[`bfs-equivariance-proof.md`](bfs-equivariance-proof.md) に記載の通り、
BFS 出力のリスト等号は探索順序依存で偽になりうる。

Gravity の `floatingUnits` は内部で `allStructuralClusters` → `structuralCluster` →
`structuralBfs` を呼ぶため、同じ問題を持つ。
`floatingUnits_perm_rotate180` は `List.Perm`（順序無視の置換等価）で述べる必要がある。

---

## `foldl` の交換法則を活用する証明パターン

`settle_foldl_eq` のような「ソート後の foldl が同値」を示す際、
個々の操作（settleStep）の交換法則から foldl 全体の等価性を導くパターンがある。

- `settleStep_comm_ne_dir`: 方角列を共有しない落下単位同士の settleStep は交換可能
- `foldl_settle_head_swap`: 循環ペアでの隣接要素交換
- `foldl_pointwise_ext`: positions の `.any` 等価から foldl 結果の等価を導く

---

## `sortFU_foldl_flatMap_any_eq` は偽命題（削除済み）

旧補題 `sortFU_foldl_flatMap_any_eq` は以下の仮説で主張していた:
- flatMap positions .any の等価性
- pairwise 位置素性
- Nodup

**これは偽である。** 理由: flatMap any 等価 + pairwise 位置素は「同じ位置集合の異なるグルーピング」
を許容する。異なるグルーピング（例: クラスタの分割方法が異なる）では、各ユニットの着地距離が
グルーピングに依存するため、foldl 結果が変わりうる。

```
反例: l1 = [{(0,E),(1,E)}], l2 = [{(0,E)}, {(1,E)}]
  l1: クラスタとして一体で落下 → 最下位が着地したら全体停止
  l2: ピンとして個別に落下 → (0,E) が先に着地、(1,E) は (0,E) に阻まれることも
```

### 修正: 3 つの正しい sorry に分解

`sortFU_foldl_rotate180_eq` を以下の 3 補題から構成:

1. **`floatingUnits_spb_antisymm`**: floatingUnits 要素間の shouldProcessBefore 反対称性
   - 構造クラスタの幾何制約（clusters_no_adj_same_layer + reachable_visits_intermediate_layer）から導出
   - pin-pin / pin-cluster は ℕ 順序から直接。cluster-cluster が本質

2. **`sortFU_foldl_perm_eq`**: Perm 入力に対する sortFallingUnits foldl の不変性
   - 反対称性の下で tied ペアは方角素 → foldl_swap_at_eq で吸収
   - 帰納法のアプローチ: Perm.swap ケースが核心（tied swap → foldl 不変の伝搬）

3. **`floatingUnits_rotate180_perm_any`**: 回転対応の構成
   - fU s.r180 の Perm l' で l' と (fU s).map r180 が pointwise .any 等価
   - rotation が構造結合を保存 → クラスタが 1 対 1 に対応

---

## 構造クラスタの反順序性の証明構造

`floatingUnits_spb_antisymm` の cluster-cluster ケース:

1. shouldProcessBefore u v = true → ∃ d₁, u.min_d₁ < v.min_d₁
2. shouldProcessBefore v u = true → ∃ d₂, v.min_d₂ < u.min_d₂
3. d₁ ≠ d₂（同一方角なら < の反対称性で矛盾）
4. 両クラスタは d₁ と d₂ の両方に位置を持つ
5. クラスタ内のパスは d₁ ↔ d₂ 間で方角遷移を含む → 遷移層で隣接方角の位置が存在
6. 相手クラスタも reachable_visits_intermediate_layer により遷移層を通過
7. clusters_no_adj_same_layer で矛盾

pin-pin と pin-cluster は ℕ 順序から直接導出可能。

---

## `sortFU_spb_order_on_fU` 任意入力版は偽定理

`sortFU_spb_order_on_fU` は以下を主張:

> 任意のリスト l（floatingUnits の要素を任意の順序で並べたもの）に対し、
> `shouldProcessBefore(a, b) = true` ならば `posIn a (sortFallingUnits l) < posIn b (sortFallingUnits l)`

これは **偽** である。

### 反例

5 層シェイプ（Layer 0 全空）:

```
Layer 1: SE=crystal, SW=crystal
Layer 2: SE=crystal, SW=pin (pin_e)
Layer 3: NE=pin (pin_a), SE=crystal
Layer 4: NE=crystal, SE=crystal
```

floatingUnits:
- cluster(NE@4, SE@1-4, SW@1, tb=9)
- pin_a(NE@3, tb=4)
- pin_e(SW@2, tb=3)

shouldProcessBefore 関係: pin_a→cluster (NE:3<4), cluster→pin_e (SW:1<2), pin_a/pin_e は tied

入力 [cluster, pin_a, pin_e] → sortFallingUnits = [pin_e ti, pin_a, cluster]
→ shouldProcessBefore(cluster, pin_e)=true だが posIn cluster=2 > posIn pin_e=0: **違反**

6 入力順列中 4 つで sortFallingUnits 出力が shouldProcessBefore 順序に違反する。

### 根本原因

`insertSorted` のグリーディ挿入:
1. tied ペアの tiebreaker 比較で早期挿入が発生
2. 挿入位置より後方の要素との shouldProcessBefore 関係がチェックされない
3. 結果として、shouldProcessBefore-related 要素が逆順になりうる

### 重要な知見

- **`process_rotate180` 自体は TRUE**: 実際の計算は常に自然順序（floatingUnits の出力順）を使用
- **自然順序では sortFallingUnits は正しく動作**: 6 順列中、自然順序を含む 2 順列は OK
- **問題は中間補題の過度な一般化**: settle_foldl_eq の l_mid が任意順序になりうる
- **修正方向**: l_mid の順序差分が tied-only であることを証明 or 別アプローチ

### insertSorted の tiebreaker が危険な条件

3 要素 a, b, c で:
- a と b が tied（方角列非共有）
- b と c が shouldProcessBefore 関係（方角列共有）
- a.tb ≤ b.tb（tiebreaker で a が b の前に入る）

この場合、入力順 [b, c, a] → insertSorted:
1. b → [b]
2. c: shouldProcessBefore(b,c)=true → skip b → [b, c]
3. a: a と b は tied, a.tb ≤ b.tb → a を b の前に挿入 → [a, b, c]

しかし shouldProcessBefore(c, a) が true の場合（c が a より前に来るべき）、a が c より前になり違反。
insertSorted は a の挿入時に c をチェックしない（b の前で停止するため）。

---

## `sortFU_spb_one_way_order` は floatingUnits 上でも偽（2026-04-04 第3セッションで発見）

S-3 (`sortFU_spb_one_way_order`) は **floatingUnits の制約下でも偽** と判明。

### 反例

```
a = pin(2, NE)
b = cluster[(4, NE), (4, SE)]
c = pin(6, SE)

shouldProcessBefore: a→b (NE:2<4), b→c (SE:4<6), a/c は tied (方角素)
→ NON-TRANSITIVE: shouldProcessBefore(a,b)=T, shouldProcessBefore(b,c)=T, shouldProcessBefore(a,c)=F
```

入力 `l = [c, a, b]` → `sortFallingUnits = [b, c, a]`:
- `posIn a = 2 > posIn b = 0` → shouldProcessBefore(a,b)=true なのに b の方が前 → **S-3 違反**

### 根本原因

shouldProcessBefore が floatingUnits 上でも**非推移的**。3 要素 a, b, c で shouldProcessBefore(a,b)=T, shouldProcessBefore(b,c)=T
だが shouldProcessBefore(a,c)=F（方角素の場合）が成立する。
insertSorted のグリーディ挿入はこの非推移性を処理できず、期待順序を逆転させる。

### 教訓

- **shouldProcessBefore の準推移性を前提とした S-3 のアプローチは全面的に不可**
- floatingUnits の制約でも非推移三角形は排除されない（pin と cluster の方角が異なるため）
- 代替として、sortFallingUnits の反転ペアが **direction-disjoint** であることを直接証明するアプローチ (S-4) に切り替え

---

## `placeFallingUnit` (foldl settle) は non-commutative（2026-04-04 第3セッションで確認）

`placeFallingUnit` は一般には非可換。**方角を共有する one-way ペアで foldl 結果が異なる**。

計算確認: one-way shouldProcessBefore ペアのうち方角共有するもの（例: pin(2,NE) と cluster[(4,NE),(4,SE)]）は
`foldl [a,b] ≠ foldl [b,a]` となる。

→ **sortFallingUnits は本質的に必要**。foldl settle が入力のすべての置換に対して不変ということはない。

→ 可換になるのは **direction-disjoint** なペアのみ (`settleStep_comm_ne_dir` で証明済み)。

---

## l_mid と l2 の反転は常に tied（2026-04-04 第3セッションで確認）

`settle_foldl_eq` の l_mid = (fU s).map g と l2 = fU(s.r180) の sortFallingUnits 出力間の反転ペアは
**常に tied (shouldProcessBefore 双方 false)** であることが計算で確認された（10+ shapes 全て）。

### 理由の構造的分析

1. `allValid` (= `allIsolatedPins ++ allStructuralClustersList`) は **layer 昇順** で列挙
2. `rotate180` は**レイヤ不変**（方角のみ NE↔SW, SE↔NW 回転）
3. one-way ペアは**同一方角の異なる minLayer** で順序が決まる
4. layer 昇順の列挙 + r180 のレイヤ不変性 → one-way ペアの相対順序は l_mid と l2 で同一
5. l_mid と l2 で順序が異なるのは tied ペア（方角素で shouldProcessBefore 双方 false）のみ

### 証明への影響

sortFallingUnits の入力（l_mid, l2）間の反転が tied-only であることが示されれば、
sortFallingUnits 出力間の反転も tied → direction-disjoint → foldl 結果一致。
これが S-4 (`sortFallingUnits_inversion_dir_disjoint`) の証明の核心。

---

## `shouldProcessBefore_no_mutual` の証明戦略（2026-04-04 第3セッションで完了）

### d1 = d2 ケース
`lu < lv ∧ lv < lu` → `omega` で即座に矛盾。

### d1 ≠ d2 ケース — 4-horizontal-step 矛盾戦略

1. **方角 witness の抽出**: shouldProcessBefore(u,v)=T → ∃ d1, u.min(d1) < v.min(d1)。
   shouldProcessBefore(v,u)=T → ∃ d2, v.min(d2) < u.min(d2)。d1 ≠ d2。
2. **minLayerAtDir の witness**: u は d1 に位置を持つ → ∃ p ∈ u.positions, p.dir = d1
3. **クラスタ内パスの水平ステップ**: u が d1 と d2 に位置を持つ場合、
   BFS パス中に「水平ステップ」（同レイヤ隣接方角への遷移）が存在。
   `genReachable_diff_dir_horizontal` でこれを形式化。
4. **隣接方角の占有**: 水平ステップの遷移元位置 p に対し、p.dir = d1 かつ
   同レイヤで隣接方角 d2 に別の位置が存在。
5. **位置非共有との矛盾**: v も d2 の位置を持ち、v.min(d2) ≤ p.layer なので
   v がその層の d2 に位置を持つ → u も同層の d2 に位置を持つ → 位置共有で矛盾。

### 使用した補題
- `genReachable_diff_dir_horizontal`: クラスタ内の方角遷移で水平ステップ存在
- `minLayerAtDir_le_of_mem`: minLayer 以上のレイヤに位置が存在

---

## `insertSorted_preserves_relative_order` の証明戦略（2026-04-04 第3セッションで完了）

`insertSorted_split` で挿入位置 k を取得し、3 ケース分岐:
- k ≤ pos_a: u は a の前に挿入 → a, b は drop 部分にそのまま残り、prefix が [u] ++ take k
- pos_a < k ≤ pos_b: u は a と b の間に挿入 → a は take 部分、b は drop 部分
- k > pos_b: u は b の後に挿入 → a, b は take 部分にそのまま残り、suffix に [u] ++ drop k

各ケースで List の take/drop 分割を manipulate し、`prefix_ ++ [a] ++ mid ++ [b] ++ suffix_` 形式の witness を構成。
