# Gravity 180° 回転等変性 証明の知見

`Gravity.lean` における `process_rotate180`（180° 回転等変性）の証明で得られた
Gravity 固有の知見。汎用的な Lean 4 の Tips は [`lean-proof-tips.md`](../lean/lean-proof-tips.md) を参照。

> **注記（2026-04-09）**: `settle_foldl_eq` は Wave 9 で sorry=0 を達成済み。
> 旧証明チェーン（`shouldProcessBefore`/`insertSorted` ベース、Wave 1-5）は
> `fallingUnitOrd` 全順序ソートに置き換えられ、旧チェーン固有の偽定理分析・
> 証明計画は本ファイルから削除した。偽定理カタログは
> [`false-theorem-catalog.md`](false-theorem-catalog.md) に集約。

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

## `placeFallingUnit` (foldl settle) は non-commutative

`placeFallingUnit` は一般には非可換。**方角を共有する one-way ペアで foldl 結果が異なる**。

計算確認: one-way shouldProcessBefore ペアのうち方角共有するもの（例: pin(2,NE) と cluster[(4,NE),(4,SE)]）は
`foldl [a,b] ≠ foldl [b,a]` となる。

→ **ソートは本質的に必要**。foldl settle が入力のすべての置換に対して不変ということはない。

→ 可換になるのは **direction-disjoint** なペアのみ (`settleStep_comm_ne_dir` で証明済み)。

---

## `shouldProcessBefore_no_mutual` の証明戦略

`shouldProcessBefore_no_mutual`: floatingUnits 間で shouldProcessBefore 双方向 true は不可。

### d1 = d2 ケース
`lu < lv ∧ lv < lu` → `omega` で即座に矛盾。

### d1 ≠ d2 ケース — 4-horizontal-step 矛盾戦略

1. **方角 witness の抽出**: shouldProcessBefore(u,v)=T → ∃ d1, u.min(d1) < v.min(d1)。
   shouldProcessBefore(v,u)=T → ∃ d2, v.min(d2) < u.min(d2)。d1 ≠ d2。
2. **minLayerAtDir の witness**: u は d1 に位置を持つ → ∃ p ∈ u.positions, p.dir = d1
3. **クラスタ内パスの水平ステップ**: u が d1 と d2 に位置を持つ場合、
   クラスタ連結パス中に「水平ステップ」（同レイヤ隣接方角への遷移）が存在する。
   `genReachable_diff_dir_horizontal` でこれを形式化。
4. **隣接方角の占有**: 水平ステップの遷移元位置 p に対し、p.dir = d1 かつ
   同レイヤで隣接方角 d2 に別の位置が存在。
5. **位置非共有との矛盾**: v も d2 の位置を持ち、v.min(d2) ≤ p.layer なので
   v がその層の d2 に位置を持つ → u も同層の d2 に位置を持つ → 位置共有で矛盾。

### 使用した補題
- `genReachable_diff_dir_horizontal`: クラスタ内の方角遷移で水平ステップ存在
- `minLayerAtDir_le_of_mem`: minLayer 以上のレイヤに位置が存在
