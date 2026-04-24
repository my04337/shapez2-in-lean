# 等変性・交換則 証明パターン集

S2IL プロジェクトの Lean 4 形式化で確立された、
等変性（equivariance）・交換則（commutativity）の証明パターンを集約する。

個別の知見ドキュメント:
- [`gravity-equivariance-analysis.md`](gravity-equivariance-analysis.md) — Gravity 固有の等変性知見

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
| `shatterOnCut` | allCrystalClusters + clearPositions |
| `stack` | placeAbove + shatter + gravity + truncate |

### 注意: 中間表現の等変性の粒度

- **リスト等号**で中間結果の等変性を述べると偽命題になりがち（探索順序やソート順序に依存する実装で外がしやすい）
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

## パターン 7: rotate180 を rotateCW の 2 重適用から導出

### 概要

`Shape.rotate180_eq_rotateCW_rotateCW : s.rotate180 = s.rotateCW.rotateCW` を使い、
`operator_rotate180_comm` を `operator_rotateCW_comm` の 2 回適用で導出するパターン。
**片方向（rotateCW）だけ証明すれば rotate180 側は 1 行で自動化される。**

### 適用例（完成）

- `crystallize_rotate180_comm` ← `crystallize_rotateCW_comm`
- `paint_rotate180_comm` ← `paint_rotateCW_comm`

### 1 行証明パターン

```lean
theorem operator_rotate180_comm (s : Shape) :
        (operator s).map Shape.rotate180 = operator s.rotate180 := by
    simp only [rotate180_eq_rotateCW_rotateCW, operator_rotateCW_comm]
```

### Gravity 版の計画

`waveStep_rotate180_comm` を `waveStep_rotateCW_comm` から導出する設計を採用予定。
現在は両方とも一時 axiom（2026-04-20 時点）。S3 de-axiomatization 後にこのパターンで導出する。

### 配置上の注意

導出する側（rotate180）は導出元（rotateCW）より後ろに配置する必要がある。
Equivariance.lean に rotate180 定理があり、Facade.lean に rotateCW 定理がある
場合は、rotate180 を Facade.lean 側へ移動してから 1 行証明に置換する。

---

## パターン 8: 真定理の一時 axiom 化による進捗確保

### 概要

構成的証明が複雑だが計算検証で真と確認済みの定理については、
下流の依存ビルドを通すために **一時 axiom** として導入し、
上流・下流のタスクを先行させる戦略。

### 適用条件（必須）

1. 定理が真であることを `#guard` / `#eval` / vanilla テストで計算検証済み
2. 構成的証明の骨格は存在するが、核心補題群が 3 セッション以上消費している
3. 下流タスク（依存する上位定理、他モジュール）を先に完成させたい

### 運用ルール

- `axiom` 宣言に `/-- **現状**: 一時 axiom として導入。... -/` を必ず付記
- de-axiomatization の計画手順を docstring 内に明記
- 計画資料（`docs/plans/`）に axiom 一覧と除去順序を記述
- 除去完了まで関連補助補題は削除せず `private` で保持（再利用資産）

### 適用例（Gravity, 2026-04-20）

- `waveStep_rotate180_comm` (axiom) ← S3 経由で除去予定
- `waveStep_rotateCW_comm` (private axiom) ← Perm 基盤構築で除去予定

関連補助補題（`settling_positions_any_rotateCW`, `minML_eq_rotateCW`,
`foldl_min_fu_*` 等）は Facade.lean に `private` で保持し、
de-axiomatization 時に再利用する。

### ⚠️ 注意

- axiom 導入は **プロジェクト目標 (`axioms=0`) から一時的に逸脱**する操作
- axiom の永続化は最終手段。優先度 1 のタスクが完了次第、除去に戻る
- レビュー時は axiom 導入の文書化と除去計画の存在を必ず確認する

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

---

## 操作別 等変性サマリーテーブル

> 出典: s2il-lemma-index.md（整理完了・2026-04-17 削除）

### 回転等変性テーブル

| 操作 | r180 | rCW | rCCW |
|---|---|---|---|
| `paint` | ✅ | ✅ | ✅ |
| `crystallize` | ✅ | ✅ | ✅ |
| `gravity` | ✅ (≤5L) | ✅ (≤5L) | — |
| `shatterOnFall` | — | ✅ | — |
| `shatterOnTruncate` | — | ✅ | — |
| `pinPush` | — | ✅ (≤5L) | — |
| `truncate` (Stacker) | — | ✅ | — |
| `liftUp` (PinPusher) | — | ✅ | — |
| `generatePins` (PinPusher) | — | ✅ | — |

### 非等変操作（rCW）

| 操作 | 理由 |
|---|---|
| `cut` / `halfDestroy` / `swap` | `shatterOnCut` が E-W 軸固有（`isEast`/`isWest` プレディケート）。rCW で軸回転するため非等変 |

### Machine.lean（Option ラッパー）

着色・回転・結晶化は `Option Shape.SettledShape` ベースに移行済み。
pinPush/stack/halfDestroy/cut/swap は `Option Shape` のまま（テスト互換性のため）。

| 関数 | 入力型 | 出力型 | 等変性 |
|---|---|---|---|
| `Machine.paint` | `Option SettledShape` | `Option SettledShape` | ✅ (r180/rCW/rCCW) |
| `Machine.crystallize` | `Option Shape` | `Option SettledShape` | ✅ (r180/rCW/rCCW) |
| `Machine.rotateCW` | `Option SettledShape` | `Option SettledShape` | — |
| `Machine.rotateCCW` | `Option SettledShape` | `Option SettledShape` | — |
| `Machine.rotate180` | `Option SettledShape` | `Option SettledShape` | — |
| `Machine.pinPush` | `Option Shape` | `Option Shape` | 🔲（未移行） |
| `Machine.stack` | `Option Shape × Option Shape` | `Option Shape` | 🔲（未移行） |
| `Machine.halfDestroy` | `Option Shape` | `Option Shape` | 🔲（未移行） |
| `Machine.cut` | `Option Shape` | `Option Shape × Option Shape` | 🔲（未移行） |
| `Machine.swap` | `Option Shape × Option Shape` | `Option Shape × Option Shape` | 🔲（未移行） |
| `Machine.mixColor` | `Option Color × Option Color` | `Option Color` | 変更予定なし |
