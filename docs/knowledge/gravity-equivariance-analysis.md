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

仮定は **2 要素間のペアワイズな非循環** (`spb(b,a)=false`) しか要求しないが、
第三者 `w` との 3-cycle が `insertSorted` のグリーディ挿入を狂わせる。

```
a = cluster [⟨0, .ne⟩, ⟨5, .se⟩]
b = cluster [⟨3, .ne⟩, ⟨0, .sw⟩]
w = cluster [⟨3, .sw⟩, ⟨0, .se⟩]

spb 関係: a→b (ne:0<3), b→w (sw:0<3), w→a (se:0<5)  ← 3-cycle
各ペアは 2-cycle なし (仮定を満たす):
  spb(a,b)=true, spb(b,a)=false ✓  spb(b,w)=true, spb(w,b)=false ✓  spb(w,a)=true, spb(a,w)=false ✓
```

`l = [w, a, b]` での `sortFallingUnits` の動作で b が a より前に来てしまい、
`a の position > b の position` となって定理に矛盾する。

### 教訓

1. **ペアワイズ非循環 ≠ DAG**: 全ペアの 2-cycle がなくても 3-cycle 以上が存在しうる
2. **修正方針**: `h_no_cycle` を 2-cycle 禁止から **DAG 条件** に強化するか、
   証明構造を根本的に見直す必要がある

詳細な分析は [`settle-foldl-eq-analysis.md`](settle-foldl-eq-analysis.md) を参照。

---

## `insertSorted` のグリーディ挿入の動作特性

`insertSorted u sorted fuel`:
1. sorted を先頭から順にスキャンする
2. `spb(u, v) = true` → v の前に u を挿入して停止
3. `spb(v, u) = true` → v をスキップして次へ
4. tied (spb 双方 false): tiebreaker 比較 (`tb u ≤ tb v` なら u を前に挿入)
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

1. **`floatingUnits_spb_antisymm`**: floatingUnits 要素間の spb 反対称性
   - 構造クラスタの幾何制約（clusters_no_adj_same_layer + reachable_visits_intermediate_layer）から導出
   - pin-pin / pin-cluster は ℕ 順序から直接。cluster-cluster が本質

2. **`sortFU_foldl_perm_eq`**: Perm 入力に対する sortFU foldl の不変性
   - 反対称性の下で tied ペアは方角素 → foldl_swap_at_eq で吸収
   - 帰納法のアプローチ: Perm.swap ケースが核心（tied swap → foldl 不変の伝搬）

3. **`floatingUnits_rotate180_perm_any`**: 回転対応の構成
   - fU s.r180 の Perm l' で l' と (fU s).map r180 が pointwise .any 等価
   - rotation が構造結合を保存 → クラスタが 1 対 1 に対応

---

## 構造クラスタの反順序性の証明構造

`floatingUnits_spb_antisymm` の cluster-cluster ケース:

1. spb u v = true → ∃ d₁, u.min_d₁ < v.min_d₁
2. spb v u = true → ∃ d₂, v.min_d₂ < u.min_d₂
3. d₁ ≠ d₂（同一方角なら < の反対称性で矛盾）
4. 両クラスタは d₁ と d₂ の両方に位置を持つ
5. クラスタ内のパスは d₁ ↔ d₂ 間で方角遷移を含む → 遷移層で隣接方角の位置が存在
6. 相手クラスタも reachable_visits_intermediate_layer により遷移層を通過
7. clusters_no_adj_same_layer で矛盾

pin-pin と pin-cluster は ℕ 順序から直接導出可能。
