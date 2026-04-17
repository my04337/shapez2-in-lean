# BFS 等変性の証明パターン

`CrystalBond.bfs` の 180° 回転等変性を証明する過程で得られた知見をまとめる。
BFS のような再帰関数に対して「変換後の入力で実行 = 実行してから変換」を示す場合の
実践的なパターンとアンチパターンを記録する。

---

## 背景: 何を証明したいのか

結晶結合クラスタの算出に BFS を使っており、シェイプの 180° 回転に対して
砕け散り処理が可換であることを示したい。最終目標:

```lean
-- shatterOnCut を先にやってから rotate180 しても、
-- rotate180 してから shatterOnCut しても結果が同じ
theorem shatterOnCut_rotate180_comm (s : Shape) :
        s.shatterOnCut.rotate180 = s.rotate180.shatterOnCut
```

`shatterOnCut` は内部で `allCrystalClusters → clearPositions` を呼ぶため、
BFS の結果が rotate180 でどう変わるかが証明の核心になる。

---

## 失敗したアプローチ

### ❌ アプローチ 1: リスト等号で BFS 等変性を主張

```lean
-- 最初に試みた定理文
theorem shatterTargetsOnCut_rotate180 (s : Shape) :
        s.rotate180.shatterTargetsOnCut =
        s.shatterTargetsOnCut.map QuarterPos.rotate180
```

**失敗理由**:
- `shatterTargetsOnCut` は内部で `allCrystalClusters` を呼ぶ
- `allCrystalClusters` は `allValid s` をノード一覧として BFS に渡す
- `allValid s.rotate180 = allValid s`（`layerCount` のみに依存）だが、
  `(allValid s).map rotate180 ≠ allValid s`（Direction の列挙順序が異なる）
- BFS はノード一覧の順序でフィルタするため、**探索順序**が変わる
- 探索順序が変わると visited リストも変わり、結果のリスト自体が異なる
- つまり **この定理文は偽** であり、sorry にせざるを得ない

**教訓**: BFS のリスト出力は探索順序に依存するため、
**リストの等号**で等変性を主張すると偽命題になりうる。

### ❌ アプローチ 2: 外部モジュールから private な BFS の性質を推論

元の計画では `CrystalBond.bfs` が `private` であることが障壁とされていた。
しかし `private` を解除しても、`bfs` の定義を見てアプローチ 1 を試みる限り、
根本問題（リスト等号が偽）は解決しない。

**教訓**: `private` の壁は確かに存在するが、真の障壁は定理文の正しさ。
アクセス可能になっても、リスト等号の定理文を立てればやはり詰まる。

### ❌ アプローチ 3: fuel 帰納法で `simp only [bfs]` を最初に適用

```lean
induction fuel generalizing visited queue with
| succ n ih =>
    simp only [bfs]       -- ← ここで問題発生
    cases queue with ...
```

**失敗理由**:
- `queue.map QuarterPos.rotate180` の形のまま `bfs` を展開すると、
  `match queue.map ... with` のパターンマッチが展開されない
- `simp only [bfs]` は一部の分岐を展開するが、`if-then-else` の
  条件部分まで展開されてゴールが複雑化する

### ❌ アプローチ 4: `congr 1` + `funext` でフィルタ述語の等価性を証明

```lean
rw [list_filter_map_rotate180]
congr 1
funext p
```

**失敗理由**:
- `List.filter` に渡される述語はラムダ式で、LHS と RHS の述語が
  構文的に異なる形をしている
- `congr 1` はリストに `congr` を適用するが、`funext` は
  `List.filter` の述語引数が関数等号 `=` でラップされた形ではなく、
  `congr` が生成するゴールに `@funext` が型マッチしない

**教訓**: `List.filter pred1 l = List.filter pred2 l` で `pred1 = pred2`
を示す場合、`congr 1` + `funext` が型マッチしないことがある。
述語の等価性は外部で証明するか、リスト帰納法で直接示す方が確実。

### ❌ アプローチ 5: BFS 帰納法の内部で別の帰納法（nested induction）

```lean
-- fuel の帰納法の中で allPos の帰納法を使おうとした
induction fuel generalizing visited queue with
| succ n ih =>
    ...
    have h_neighbors : ... := by
        induction allPos with  -- ← nested induction
        | cons a as ih_a => ... exact congrArg _ ih_a  -- ❌ 型が合わない
```

**失敗理由**:
- 外側の `induction fuel ... with | succ n ih =>` で生成される `ih` は
  `∀ (visited queue : List QuarterPos), bfs ... = ...` の型を持つ
- 内側で `induction allPos` すると、`as` に簡約された `allPos` と
  外側の `ih` が参照する `allPos` が不整合を起こす
- `ih_a` の型が「外側 ih の allPos が as になった版」になってしまい、
  使いたい箇所の型と合わない

**教訓**: 再帰関数の帰納法内部で別のリストに対する帰納法が必要な場合、
**必ず外部の独立した補題として切り出す**こと。

---

## ✅ 成功したアプローチ

### 二段構成: BFS は mapped allPos で証明 + clearPositions レベルで接続

#### 戦略の核心

1. **BFS 等変性** は `(allPos.map rotate180)` を渡した場合について証明する
   （allPos の要素が rotate180 済みなら、BFS 結果も素直に map される）
2. **最終定理** は `clearPositions` レベルで述べる
   （リスト順序が異なっても、空にする位置の「集合」が同じなら clearPositions 結果は同一）

#### 1. mapped allPos での BFS 等変性（fuel 帰納法）

```lean
private theorem bfs_rotate180 (s : Shape)
        (allPos visited queue : List QuarterPos) (fuel : Nat) :
        bfs s.rotate180
            (allPos.map QuarterPos.rotate180)
            (visited.map QuarterPos.rotate180)
            (queue.map QuarterPos.rotate180) fuel =
        (bfs s allPos visited queue fuel).map QuarterPos.rotate180
```

**証明のコツ**:
- `cases queue` → `nil` ケースは `simp [bfs]` で閉じる
- `cons` ケースでは **`show` で LHS を明示的に cons 形式に書き換え**てから
  `simp only [bfs]` を適用する。これにより `List.map` → `cons` の簡約が
  `bfs` の展開と同時に行われる
- `split` で `if visited.any (· == pos)` の分岐を処理
- neighbors のフィルタ等変性は **独立した補題** `filter_isBonded_map_rotate180` で処理

```lean
| cons pos rest =>
    show bfs s.rotate180 (allPos.map QuarterPos.rotate180)
        (visited.map QuarterPos.rotate180)
        (pos.rotate180 :: rest.map QuarterPos.rotate180) (n + 1) = ...
    simp only [bfs]
    rw [list_any_map_rotate180]
    split
    · exact ih visited rest
    · rw [filter_isBonded_map_rotate180, ← List.map_append]
      exact ih (pos :: visited) (rest ++ ...)
```

#### 2. ヘルパー補題は必ず外部に切り出す

BFS 帰納法の中で使う以下の補題は全て independent に証明する:

| 補題 | 内容 | 証明方法 |
|---|---|---|
| `quarterPos_beq_rotate180` | `(p.rotate180 == q.rotate180) = (p == q)` | `show` で BEq 展開 + `simp` |
| `list_any_map_rotate180` | `(l.map r180).any (· == p.r180) = l.any (· == p)` | `List` 帰納法 |
| `list_any_cons_rotate180` | cons の any と rotate180 | `simp` + 上記2補題 |
| `filter_isBonded_map_rotate180` | BFS neighbors フィルタの等変性 | `List` 帰納法 + `isBonded_rotate180` |

#### 3. 最終定理は clearPositions レベルに引き上げる

```lean
-- ❌ リスト等号（偽命題になりうる）
shatterTargetsOnCut s.rotate180 = (shatterTargetsOnCut s).map rotate180

-- ✅ clearPositions 結果の等号（正しい命題）
clearPositions s.rotate180 (shatterTargetsOnCut s.rotate180)
= clearPositions s.rotate180 ((shatterTargetsOnCut s).map rotate180)
```

そして `shatterOnCut_rotate180_comm` は:
```lean
-- clearPositions_rotate180: (s.clearPositions ps).rotate180
--     = s.rotate180.clearPositions (ps.map rotate180)
-- と組み合わせる
theorem shatterOnCut_rotate180_comm (s : Shape) :
        s.shatterOnCut.rotate180 = s.rotate180.shatterOnCut := by
    simp only [shatterOnCut]
    rw [clearPositions_rotate180]
    exact (clearPositions_shatterTargetsOnCut_rotate180_eq s).symm
```

---

## 残タスクへの指針

clearPositions レベルの sorry を解消するには、以下の **2つのアプローチ** がある:

### 方針 A: clearPositions の順序不変性

`setQuarter s p .empty` と `setQuarter s q .empty` が可換であること
（異なる位置への `.empty` 設定は順序に依存しない）を証明し、
clearPositions が位置リストの「集合」にのみ依存することを示す。

**利点**: 汎用的で他の場面にも転用可能
**課題**: `setQuarter` の可換性自体の証明が `List.set` の可換性を要求する

### 方針 B: BFS 結果の集合等価性

BFS が十分な fuel で全到達可能頂点を発見することを証明し、
allPos の順序が異なっても到達可能頂点の**集合**が同一であることを示す。
この集合等価性 + 方針 A の clearPositions 順序不変性で完了する。

**利点**: BFS の完全性が証明でき、他の定理にも活用可能
**課題**: BFS の完全性証明自体がかなり重い

### 推奨: 方針 A を先に

方針 A の `setQuarter_empty_comm` は比較的自己完結しており、
`clearPositions` の順序不変性が得られれば、BFS 結果のリスト順序差異を
吸収できる。方針 B は方針 A だけでは不十分な場合に追加で検討する。

---

## 汎用的な教訓

| 問題 | 回避策 |
|---|---|
| BFS 結果のリスト等号を主張 | リスト等号は探索順序に依存するため偽命題になりうる。**結果の適用先**（clearPositions 等）のレベルで等号を述べる |
| `private` 関数の証明 | 同一モジュール内に証明を追加する。import を増やしても OK |
| 再帰帰納法内部で別の帰納法 | 必ず独立した補題として切り出す。nested induction は型不整合の原因 |
| `simp only [再帰関数]` で match が展開されない | `show` で LHS を具体的な cons 形式に書き換えてから展開する |
| `congr 1` + `funext` で `List.filter` の述語等価性 | 型マッチしない場合あり。リスト帰納法で直接証明するか、独立補題で filter 全体の等変性を示す |
| `BEq` 等価性の rotate180 保存 | `show` で `BEq` を `&&` + フィールドの `==` に展開し、各フィールドの保存を示す |

---

## 参考: 補題の依存関係

```
quarterPos_beq_rotate180
  ← dir_beq_rotate180'

list_any_map_rotate180
  ← quarterPos_beq_rotate180

list_any_cons_rotate180
  ← quarterPos_beq_rotate180
  ← list_any_map_rotate180

isBonded_rotate180
  ← isBondedInLayer_rotate180 ← getQuarter_rotate180, Direction.adjacent_rotate180
  ← isBondedCrossLayer_rotate180 ← getQuarter_rotate180

filter_isBonded_map_rotate180
  ← isBonded_rotate180
  ← list_any_cons_rotate180

bfs_rotate180
  ← list_any_map_rotate180      (visited チェック)
  ← filter_isBonded_map_rotate180  (neighbors フィルタ)
  ← List.map_append             (キュー結合)

crystalCluster_rotate180_mapped
  ← bfs_rotate180

clearPositions_rotate180         (Shatter.lean、証明済み)
  ← setQuarter_rotate180_empty

shatterOnCut_rotate180_comm
  ← clearPositions_rotate180
  ← clearPositions_shatterTargetsOnCut_rotate180_eq  (sorry)
```

## 参考: 実装ファイル

- `S2IL/Behavior/CrystalBond.lean` — BFS 等変性の証明
- `S2IL/Behavior/Shatter.lean` — 砕け散り等変性の証明
- `S2IL/Behavior/Cutter.lean` — 切断等変性の最終目標
