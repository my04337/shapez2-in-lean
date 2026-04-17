# 等変性・交換則 証明パターン集

S2IL プロジェクトの Lean 4 形式化で確立された、
等変性（equivariance）・交換則（commutativity）の証明パターンを集約する。

個別の知見ドキュメント:
- [`gravity-equivariance-analysis.md`](gravity-equivariance-analysis.md) — Gravity 固有の等変性知見
- [`bfs-equivariance-proof.md`](bfs-equivariance-proof.md) — BFS 等変性の知見

---

## パターン 1: pointwise any 等価 → foldl 等価

### 概要

2 つのリスト `l1`, `l2` が各インデックスで `.any (· == p)` 等価であるとき、
ソート後の `foldl f` 結果が一致する。

### 適用条件

- `l1` と `l2` が同じ長さ
- 各 `i` で `l1[i].positions.any (· == p) = l2[i].positions.any (· == p)`
- `f` が positions の `.any` にのみ依存する操作
- ソート比較関数が `.any` にのみ依存する（`shouldProcessBefore_ext` / `fallingUnitOrd` の `canonicalKey_eq_of_any_eq`）

### 使用箇所

- `settle_foldl_eq` Phase 1: `(floatingUnits s).map r180` と `(floatingUnits s).map g` が pointwise any 等価

---

## パターン 2: Perm + 隣接可換 → foldl 等価（バブルソート帰納法）

### 概要

`l1.Perm l2` かつ全ての隣接反転ペアが可換（direction-disjoint）であるとき、
`l1.foldl f = l2.foldl f` が成立する。バブルソート的な反転数帰納法で証明する。

### 適用条件

- `l1.Perm l2`（置換等価）
- 全ての隣接反転ペア `(a, b)` に対して `f a ∘ f b = f b ∘ f a`
- 反転 = `posIn(a, l1) > posIn(b, l1)` かつ `posIn(a, l2) < posIn(b, l2)`

### 実装

```lean
-- foldl_eq_of_perm_tied_adj_comm
-- 帰納法: invCount(l1, l2) に対する強帰納法
-- 基底: invCount = 0 → l1 = l2
-- 帰納: 隣接反転を見つけて swap → invCount 減少 → IH 適用
```

### 核心的な補助補題

| 補題 | 役割 |
|---|---|
| `invCount_adj_swap_lt` | 隣接反転 swap で転置数が減少 |
| `foldl_settle_swap_at` | 方角素 swap → foldl 不変 |
| `settleStep_comm_ne_dir` | 方角素ペアの settleStep 可換 |

### 教訓

- バブルソート帰納法は `Perm` + 「要素ペアの可換性」を示す場面に汎用的
- 可換性の条件が「全ペア」でなく「反転ペア」に限定できるのが強み
- `List.Perm.foldl_eq'` は全ペア可換を要求するが、こちらは反転ペアのみ

---

## パターン 3: BFS 列挙の等変性（.any メンバーシップ）

### 概要

BFS の出力に対して「リスト等号」で等変性を主張すると**偽命題**になる。
代わりに `.any (· == p)` メンバーシップレベルで等変性を述べる。

### なぜリスト等号が偽か

- BFS はノード一覧 `allPos` の順序で neighbors をフィルタする
- `allPos.map rotate180 ≠ allPos`（Direction の列挙順序が異なる）
- 探索順序が変わると visited リストも変わり、出力リストの順序が異なる

### 正しい等変性の述べ方

```lean
-- ❌ 偽命題（リスト等号）
shatterTargetsOnCut s.rotate180 = (shatterTargetsOnCut s).map rotate180

-- ✅ 正しい命題（clearPositions レベルで接続）
clearPositions s.rotate180 targets1 = clearPositions s.rotate180 targets2

-- ✅ 正しい命題（.any メンバーシップ）
∀ p, l1.any (· == p) = l2.any (· == p)
```

### BFS 等変性の証明パターン

1. **mapped allPos での BFS 等変性**を fuel 帰納法で証明
   - `bfs s.r180 (allPos.map r180) (visited.map r180) (queue.map r180) fuel`
   - `= (bfs s allPos visited queue fuel).map r180`
2. **最終定理は clearPositions レベルに引き上げ**
   - リスト順序が異なっても空にする位置の「集合」が同じなら結果一致

### 実装上のコツ

- `show` で LHS を具体的な cons 形式に書き換えてから `simp only [bfs]` を適用
- neighbors のフィルタ等変性は独立補題 `filter_isBonded_map_rotate180` で処理
- 再帰帰納法内部で別の帰納法が必要な場合は必ず独立補題として切り出す

### CrystalBond での具体的な適用チェーン

CrystalBond モジュールでは以下の層状構成で BFS 等変性を証明済み:

```
filter_isBonded_map_rotate180          -- neighbors フィルタの等変性
    ↓
genericBfs_isBonded_rotate180          -- BFS 全体の等変性（帰納法）
    ↓
cluster_rotate180                      -- Finset クラスタの等変性
```

`isBonded_rotate180` → `genericBfs_isBonded_rotate180` の帰納法構成は構造的に明快で、
BFS の各ステップで rotate180 マッピングの整合性を維持する。

---

## パターン 4: direction-disjoint → settleStep 可換

### 概要

2 つの FallingUnit が方角列を共有しない（direction-disjoint）場合、
それらの settleStep は交換可能。

### 原理

- `settleStep` は各方角列（NE, SE, SW, NW）独立に最小レイヤを操作
- 方角を共有しないユニット同士は互いの着地距離に影響しない
- したがって処理順序に依存しない

### 実装

```lean
-- settleStep_comm_ne_dir
-- 方角素ペアの settleStep は可換
-- placeFallingUnit(s, u1, u2) = placeFallingUnit(s, u2, u1)
```

### 使用箇所

- `foldl_settle_head_swap`: 方角素隣接要素の swap → foldl 不変
- `foldl_settle_swap_at`: prefix 付き方角素 swap → foldl 不変
- `foldl_eq_of_perm_tied_adj_comm` のコールバック

---

## パターン 5: operator ∘ rotate = rotate ∘ operator 型の等変性

### 概要

操作 `op` と回転 `r` が以下の意味で可換であることを示すパターン:
```
op(r(s)) = r(op(s))
```

### 戦略

1. `op` を構成要素に分解（例: gravity = floatingUnits + sortFallingUnits + foldl settle）
2. 各構成要素について回転等変性を個別に証明
3. 合成して最終等変性を導出

### 分解の具体例

| 操作 | 分解 |
|---|---|
| `gravity.process` | floatingUnits + sortFallingUnits + foldl placeFallingUnit |
| `shatterOnCut` | allCrystalClusters (BFS) + clearPositions |
| `stack` | placeAbove + shatter + gravity + truncate |

### 注意: 中間表現の等変性の粒度

- **リスト等号**で中間結果の等変性を述べると偽命題になりがち（BFS 順序問題）
- **集合等価**（`.any` メンバーシップ）や **結果適用先**レベルで述べるのが安全
- 各分解ステップで必要な等変性の粒度を事前に確認する

---

## パターン 6: 東西入れ替え型の等変性（rotate180 + cut/swap）

### 概要

180° 回転（rotate180）でシェイプの東側と西側が入れ替わるため、
切断系操作（cut, halfDestroy, swap）の等変性は「出力が入れ替わる」形で成立する。

### 基盤補題

- `Layer.eastHalf_rotate180`: `l.eastHalf.r180 = l.r180.westHalf`
- `Layer.westHalf_rotate180`: `l.westHalf.r180 = l.r180.eastHalf`
- `Layer.combineEastWest_rotate180`: `combineEastWest(e, w).r180 = combineEastWest(w.r180, e.r180)`

### 定理の形

```lean
-- cut: 出力タプルの東西が入れ替わる
cut(s).1.map r180 = cut(s.r180).2
cut(s).2.map r180 = cut(s.r180).1

-- halfDestroy: 東側出力(=cut.1)が回転で西側(=cut.2)に
halfDestroy(s).map r180 = s.r180.cut.2

-- swap: 出力タプルの東西が入れ替わる（主ケースのみ）
swap(s1, s2).1.map r180 = swap(s1.r180, s2.r180).2
swap(s1, s2).2.map r180 = swap(s1.r180, s2.r180).1

-- combineHalves: 回転で引数の東西が入れ替わる
combineHalves(a, b).r180 = combineHalves(b.r180, a.r180)
```

### 注意: swap の辺縁ケース

`swap` の settleAfterCut が `none` を返す辺縁ケース（入力が shatterOnCut+settle で空になる場合）では、
`eastHalf` 選択が r180 等変でないため、出力入れ替え型の等変性が成立しない。
`swap_rotate180_comm` は `settleAfterCut.isSome` 仮説で主ケースに限定して証明されている。

---

## アンチパターン集

### ❌ sortFallingUnits 出力の pointwise 等価

`sortFallingUnits(l1)` と `sortFallingUnits(l2)` が pointwise `.any` 等価であること — **偽**。
2L で 800 不一致、3L で 9072 不一致。

### ❌ flatMap .any 等価 + 位置素 → foldl 一致

flatMap `.any` の等価性と pairwise 位置素性は「同じ位置集合の異なるグルーピング」を許容する。
異なるグルーピングでは各ユニットの着地距離がグルーピング依存で foldl 結果が変わりうる。

### ❌ Perm だけで foldl 等価

`List.Perm.foldl_eq'` は全ペア可換を要求する。
方角共有ペアは非可換なので直接適用できない。反転ペアのみの可換性で十分なパターン 2 を使う。
