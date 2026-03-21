# 砕け散り (Shatter) 実装方針

結晶の砕け散り (Shatter) を Lean 4 で形式化するための実装方針と今後のロードマップ。

仕様の詳細は [`docs/shapez2/crystal-shatter.md`](shapez2/crystal-shatter.md) を参照。

---

## 1. 目的

Shapez2 の加工操作（切断・積み重ね等）には、結晶の砕け散りという副作用が伴う。
この副作用を厳密にモデル化し、加工操作の前処理として砕け散り後のシェイプを計算できるようにする。

対応する MILESTONES.md タスク: **1-2-16** (結晶の Fragile 性の形式化)

---

## 2. 前提となる既存コード

| ファイル | 関連する定義 |
|---|---|
| `S2IL/Shape/Quarter.lean` | `Quarter` 型: `empty`, `pin`, `crystal color`, `colored part color` の4コンストラクタ。`isEmpty`, `color?` 関数 |
| `S2IL/Shape/Layer.lean` | `Layer` 構造体: `ne`, `se`, `sw`, `nw` の4フィールド。`isEmpty` 関数 |
| `S2IL/Shape/Shape.lean` | `Shape` 帰納型: `single`, `double`, `triple`, `quadruple` の4コンストラクタ。`normalize`, `layers` 関数 |
| `S2IL/Shape/Color.lean` | `Color` 型: 8色の列挙型。`DecidableEq` インスタンス |
| `S2IL/Processing/Rotate.lean` | 加工操作の実装テンプレート（Layer → Shape の二段構成パターン） |

---

## 3. 実装フェーズ

### Phase 1: `Quarter.isFragile` 述語の追加

**ファイル**: `S2IL/Shape/Quarter.lean`

`Quarter` が脆弱かどうかを判定する関数を追加する。

```lean
def isFragile : Quarter → Bool
    | crystal _ => true
    | _         => false
```

シンプルなパターンマッチで定義できる。
`isEmpty` と同様のスタイルで実装する。

関連する補題:
- `isFragile_crystal`: `(crystal c).isFragile = true`
- `not_isFragile_empty`: `empty.isFragile = false`
- `not_isFragile_pin`: `pin.isFragile = false`
- `not_isFragile_colored`: `(colored p c).isFragile = false`

### Phase 2: 象限位置型と結合隣接関係の定義

**ファイル**: 新規 `S2IL/Shape/QuarterPos.lean`（または既存ファイルに追加）

シェイプ内の象限の絶対位置を表す型と、結合における隣接関係を定義する。

#### 2a. 象限位置型 `QuarterPos`

```lean
-- レイヤのインデックス (0〜3)
inductive LayerIndex where
    | l1 | l2 | l3 | l4

-- レイヤ内の方角
inductive Direction where
    | ne | se | sw | nw

-- シェイプ内の象限の絶対位置
structure QuarterPos where
    layer : LayerIndex
    dir   : Direction
```

#### 2b. 隣接関係

同レイヤ内の隣接（円環状4ペア）と上下レイヤ間の隣接を定義する。

```lean
-- 同レイヤ内で方角が隣接しているか
def Direction.adjacent : Direction → Direction → Bool
    | ne, se | se, ne => true
    | se, sw | sw, se => true
    | sw, nw | nw, sw => true
    | nw, ne | ne, nw => true
    | _, _             => false

-- 上下レイヤが隣接しているか
def LayerIndex.verticallyAdjacent : LayerIndex → LayerIndex → Bool
    | l1, l2 | l2, l1 => true
    | l2, l3 | l3, l2 => true
    | l3, l4 | l4, l3 => true
    | _, _             => false
```

### Phase 3: 結晶結合クラスタの算出

**ファイル**: 新規 `S2IL/Processing/CrystalBond.lean`

シェイプ内の結晶の結合クラスタ（連結成分）を算出する。

#### アルゴリズム

シェイプは最大4レイヤ × 4象限 = 16象限なので、単純な BFS / Union-Find で十分。

1. シェイプ内の全結晶象限を列挙する
2. 結合条件を満たすペアにエッジを張る
   - **同レイヤ内**: 方角が隣接 かつ 両方が結晶 かつ 同色
   - **上下レイヤ間**: 同方角 かつ 両方が結晶（色は問わない）
3. 連結成分を求める → 各成分が1つの結合クラスタ

Lean での実装は `List` ベースの単純な到達可能性探索（BFS/DFS）が適切。
最大16頂点なので計算量の心配は不要。

```lean
-- 結晶の結合グラフを構築し、指定位置から到達可能な全象限を返す
def Shape.crystalCluster (s : Shape) (pos : QuarterPos) : List QuarterPos := ...

-- シェイプ内の全結合クラスタを返す
def Shape.allCrystalClusters (s : Shape) : List (List QuarterPos) := ...
```

### Phase 4: `Shape.shatter` 関数

**ファイル**: 新規 `S2IL/Processing/Shatter.lean`

指定された象限位置の集合を `Quarter.empty` に置き換える関数。

```lean
-- 指定位置の象限を空に置き換える
def Shape.clearPositions (s : Shape) (positions : List QuarterPos) : Shape := ...

-- 指定位置に属するクラスタ全体を砕け散らせる
def Shape.shatterAt (s : Shape) (positions : List QuarterPos) : Shape := ...
```

関連する補題:
- `shatterAt_idempotent`: 砕け散り済みの位置に再度砕け散りを適用しても変わらない
- `shatterAt_preserves_noncrystal`: 非結晶の象限は砕け散り操作で変化しない
- `shatterAt_layerCount`: 砕け散りでレイヤ数は変わらない（normalize 前）

### Phase 5: 切断時の砕け散り対象算出

**ファイル**: `S2IL/Processing/Shatter.lean` に追加

切断操作時に砕け散る位置を算出する関数。

```lean
-- 東西に跨がるクラスタに属する全象限位置を返す
def Shape.shatterTargetsOnCut (s : Shape) : List QuarterPos := ...

-- 切断前の砕け散りを適用した結果のシェイプを返す
def Shape.shatterOnCut (s : Shape) : Shape :=
    s.shatterAt (s.shatterTargetsOnCut)
```

#### 判定ロジック

1. 全結合クラスタを列挙
2. 各クラスタについて:
   - East Half (NE, SE) に属する象限があるか
   - West Half (NW, SW) に属する象限があるか
   - 両方に存在する場合、そのクラスタ全体を砕け散り対象に追加

### Phase 6: 落下時の砕け散り対象算出

**ファイル**: `S2IL/Processing/Shatter.lean` に追加

落下操作時に砕け散る位置を算出する関数。

```lean
-- 落下対象の象限位置から、砕け散る全象限位置を返す
def Shape.shatterTargetsOnFall (s : Shape) (fallingPositions : List QuarterPos) : List QuarterPos := ...

-- 落下前の砕け散りを適用した結果のシェイプを返す
def Shape.shatterOnFall (s : Shape) (fallingPositions : List QuarterPos) : Shape :=
    s.shatterAt (s.shatterTargetsOnFall fallingPositions)
```

#### 判定ロジック

1. `fallingPositions` のうち、脆弱な象限を抽出
2. それらが属する結合クラスタを求める
3. クラスタ内の全結晶を砕け散り対象とする

---

## 4. ファイル構成（予定）

```
S2IL/
    Shape/
        Quarter.lean      ← Phase 1: isFragile 追加
        QuarterPos.lean   ← Phase 2: 新規
        Layer.lean         （変更なし）
        Shape.lean         （変更なし）
    Processing/
        CrystalBond.lean  ← Phase 3: 新規
        Shatter.lean      ← Phase 4, 5, 6: 新規
        Rotate.lean        （変更なし）
Test/
    Processing/
        CrystalBond.lean  ← Phase 3: 新規
        Shatter.lean      ← Phase 4, 5, 6: 新規
```

---

## 5. 今後の展望

本方針は砕け散り操作の算出のみを対象としている。以下は今後のタスクとして別途対応する:

- **落下操作の定義・実装**: 砕け散り後に実際の落下（空の象限を詰める処理）を行う
  - MILESTONES.md タスク 1-2-10 に対応
- **切断操作の定義・実装**: 砕け散り → 東西分離 の一連の流れ
  - MILESTONES.md タスク 1-2-1 〜 1-2-4 に対応
- **積み重ね操作との統合**: 落下 + 砕け散りの組み合わせ
  - MILESTONES.md タスク 1-2-9 〜 1-2-10 に対応
- **結晶製造機 (Crystal Generator)**: 空・ピン象限を結晶で充填する操作
  - MILESTONES.md タスク 1-2-15 に対応

---

## 6. 設計上の留意点

### Rotate.lean から学ぶパターン

既存の `Rotate.lean` では **Layer レベルの操作 → Shape レベルへの持ち上げ** という二段構成が採用されている。
砕け散りでは結合クラスタが **複数レイヤに跨がる** ため、Layer 単独では完結せず Shape レベルで直接クラスタを算出する必要がある点が回転とは異なる。

### 計算量

最大4レイヤ × 4象限 = 16頂点のグラフ探索なので、BFS/DFS のいずれでも実用上問題ない。
Lean の `List` ベースで素朴に実装しても十分高速。

### 証明戦略

砕け散り関連の定理は主に以下の方針で証明する:
- `isFragile` 関連: `decide` で自動的に解ける
- クラスタ算出関連: `List` の帰納法
- `shatterOnCut` / `shatterOnFall` 関連: 具体例を `#guard` テストで検証し、一般的な性質は必要に応じて証明
