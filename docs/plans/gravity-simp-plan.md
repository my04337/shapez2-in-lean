# Gravity.lean 証明簡略化計画

> 作成日: 2026-04-06
> 対象: `S2IL/Behavior/Gravity.lean`（~6,500 行）

---

## 0. 目標

Gravity.lean 内の裸 `simp` / 裸 `simp_all` を全て `simp only [...]` / `simp_all only [...]` に安定化し、
Mathlib 更新による証明破損リスクを排除する。

---

## 1. 現状の定量分析

| タクティク | 個数 | 対象 |
|---|---:|---|
| **裸 simp** | **186** | 安定化対象 |
| **裸 simp_all** | **17** | 安定化対象 |
| simp_all (config := ...) | 1 | 個別検討 |
| simp only | 314 | 安定化済み |
| dsimp (only) | 7 | 安全 |
| simpa | 5 | 個別検討 |

**安定化対象合計: 204 箇所**

---

## 2. セクション別ヒートマップ

| セクション | 行範囲 | 裸 simp | simp_all | 密度 | 優先度 |
|---|---|---:|---:|---|---|
| Basic equivariance | L374-878 | 14 | 0 | 27% | B |
| BFS soundness | L881-1324 | 18 | 0 | 44% | A |
| Reachability | L1325-1831 | 16 | 4 | 57% | A |
| Grounding equivariance | L1867-2210 | 8 | 1 | 31% | B |
| foldl commutativity | L2214-3091 | 31 | 4 | 38% | **S** |
| tied properties | L3092-3310 | 4 | 1 | 21% | C |
| pointwise equivalence | L3312-3610 | **29** | 0 | **67%** | **S** |
| position disjointness | L3616-3900 | 3 | 0 | 27% | C |
| auxiliary theorems | L3901-4224 | 3 | 0 | 21% | C |
| bubble sort foundations | L4225-5400 | 24 | 3 | 24% | A |
| spb_no_mutual | L5401-5600 | 9 | 0 | 82% | A |
| insertSorted etc | L5621-6450 | 23 | 4 | 37% | A |
| Shape extensions | L6451+ | 2 | 0 | 50% | C |

---

## 3. パターン分類と安定化方針

### 3.1 `simp [lemmas]`（~90 箇所、難度: ★☆☆）

最多パターン。明示的に補題を渡している。REPL の `simp?` で `simp only` の補題リストに展開可能。

```lean
-- 変換前
simp [insertSorted]
-- 変換後
simp only [insertSorted, ...]  -- simp? で取得
```

**頻出サブパターン**:
- `simp [insertSorted]`: ~10 箇所
- `simp [List.any]` / `simp [List.foldl]`: 各 ~8 箇所
- `simp [List.length_take]` (L5702-5769): 6 箇所連続

### 3.2 `simp [lemmas] at h`（~30 箇所、難度: ★☆☆）

仮説を簡約するパターン。`simp only [...] at h` に直接置換可能。

### 3.3 `simp at h`（~31 箇所、難度: ★★☆）

引数なしの仮説簡約。`simp? at h` で使用補題を特定する必要がある。

### 3.4 `<;> simp` / `<;> simp [...]`（~14 箇所、難度: ★★☆）

`cases` / `rcases` のコンビネータ内。全分岐で同一の `simp only` に置換できるか個別確認が必要。

### 3.5 `by simp` (term-mode)（~56 箇所、難度: ★☆☆）

term-mode 内の `by simp`。大半は `rotate180_rotate180` 等の自明性で、単純な `by simp only [...]` に置換可能。

### 3.6 完全裸 `simp`（~21 箇所、難度: ★★★）

何を簡約しているか不明。`simp?` で個別調査が必要。一部は `decide` / `rfl` / `omega` で直接閉じられる可能性あり。

### 3.7 `simp_all`（17 箇所、難度: ★★☆）

`simp_all?` で補題リストを取得し `simp_all only [...]` に置換。手動証明に書き換えた方が良いケースもある。

### 3.8 `simp_all (config := { decide := true })`（1 箇所）

L1394。`simp_all` + `decide` のオプション付き。`simp_all only (config := { decide := true }) [...]` に置換。

---

## 4. 実行計画

### Phase 1: バッチ処理可能なパターン（目標: ~100 箇所）

同一パターンが連続・反復する箇所を `lean-simp-stabilizer` で一括処理。

| 対象 | 箇所数 | セクション |
|---|---:|---|
| `simp [insertSorted]` | ~10 | 複数セクション |
| `simp [List.any]` | ~8 | 複数セクション |
| `simp [List.foldl]` | ~8 | 複数セクション |
| `by simp [List.length_take]` | 6 | L5702-5769 |
| `by simp` (rotate180 自明性) | ~20 | 複数セクション |
| pointwise equiv セクション一括 | 29 | L3312-3610 |

### Phase 2: セクション集中処理（目標: ~70 箇所）

密度の高いセクションを順番に処理。

1. **foldl commutativity** (L2214-3091): 31 + 4 = 35 箇所
2. **bubble sort foundations** (L4225-5400): 24 + 3 = 27 箇所
3. **insertSorted etc** (L5621-6450): 23 + 4 = 27 箇所（Phase 1 の残り）

### Phase 3: 個別対応（目標: ~34 箇所）

BFS soundness・Reachability・spb_no_mutual 等の個別調査が必要な箇所。

| 対象 | 箇所数 | 備考 |
|---|---:|---|
| BFS soundness (L881-1324) | 18 | BFS 証明構造の理解が前提 |
| Reachability (L1325-1831) | 20 | `simp_all` 4 箇所含む |
| spb_no_mutual (L5401-5600) | 9 | sorry (S-5) 周辺、要注意 |
| 完全裸 `simp` | ~21 | `simp?` での個別調査 |

---

## 5. ツールと手順

### 自動安定化

`lean-simp-stabilizer` サブエージェントでセクション単位に処理:

```
lean-simp-stabilizer: Gravity.lean:401
lean-simp-stabilizer: Gravity.lean:688
...
```

### 手動対応が必要なケース

- `<;> simp`: 各分岐のゴールが異なる場合、個別の `simp only` に分解
- 完全裸 `simp`: REPL の `simp?` で補題を特定した上で置換
- `simp_all (config := ...)`: config オプションを維持して `simp_all only` 化

### ビルド検証

Phase ごとに `lake build` を実行してリグレッションチェック。

---

## 6. 注意事項

| 注意点 | 対策 |
|---|---|
| sorry (`spb_no_chain`) 周辺の `simp` | sorry 行自体は変更不可。周辺の証明本体のみ安定化 |
| `simp` → `simp only` で証明が壊れる場合 | `simp?` の結果が不完全な場合あり。追加補題を手動特定 |
| Gravity.lean は 6,500 行で lake build が重い | Phase 単位で中間コミットし、破損時のロールバックを容易に |
| spb_no_chain の証明チェーン再構築が控えている | 命名リファクタリング（gravity-rename-plan.md）とは独立に実行可能 |

---

## 7. ドキュメント更新

安定化完了後、以下を更新する:

- [ ] `docs/plans/gravity-proof-cheatsheet.md`: 「Gravity.lean の simp 安定化完了」の記載
- [ ] `docs/plans/proof-cleanup-plan.md` Section 0: Gravity を含めた全体の裸 simp = 0 を達成
- [ ] `docs/knowledge/lean-proof-tips.md`: Gravity.lean で発見した新たなパターンがあれば追記

---

## 8. チェックリスト

- [ ] Phase 1: バッチ処理可能パターンの安定化 (~100 箇所)
- [ ] Phase 1 完了: `lake build` 通過
- [ ] Phase 2: foldl commutativity セクション (35 箇所)
- [ ] Phase 2: bubble sort foundations セクション (27 箇所)
- [ ] Phase 2: insertSorted etc セクション (残り)
- [ ] Phase 2 完了: `lake build` 通過
- [ ] Phase 3: BFS soundness (18 箇所)
- [ ] Phase 3: Reachability + simp_all (20 箇所)
- [ ] Phase 3: spb_no_mutual (9 箇所)
- [ ] Phase 3: 完全裸 simp (21 箇所)
- [ ] Phase 3 完了: `lake build` 通過
- [ ] ドキュメント更新
