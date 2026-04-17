# 文字列ラウンドトリップ定理の証明パターン

> **注意**: 本文書は Shape 型が帰納型（`single`/`double`/`triple`/`quadruple`）だった
> 時期に作成された。Shape は構造体 `{ layers : List Layer, layers_ne : layers ≠ [] }`
> にリファクタリング済みだが、`List Char` レベルでの証明戦略や
> `String` カーネル関数の回避パターンは引き続き有効である。

`ofString? (toString x) = some x` 形式のラウンドトリップ定理を Lean 4 で証明する際のノウハウ。
本プロジェクトの `Shape.ofString_toString` 定理の実装過程で得られた知見をまとめる。

---

## 背景: なぜ難しいのか

Lean 4 の `String` 型は内部的に UTF-8 バイト列で実装されており、`String.splitOn` や `String.intercalate` などの標準ライブラリ関数はカーネルレベルの最適化された実装を持つ。これらは **定理証明の簡約（`simp` / `unfold` / `rfl`）で展開できない** ケースが多く、文字列操作のラウンドトリップを直接証明することが極めて困難になる。

---

## 失敗したアプローチ

### ❌ アプローチ 1: `String.splitOn` + `String.intercalate` の直接的ラウンドトリップ

```lean
-- toString: String.intercalate で結合
-- ofString?: String.splitOn で分割
-- → splitOn (intercalate sep parts) = parts を示せばよい?
```

**失敗理由**:
- `String.splitOn` は内部で `@[irreducible] String.splitOnAux` に委譲される
- `@[irreducible]` が付いているため `unfold` / `simp` で展開不可能
- `native_decide` は全称命題（`∀ s : Shape, ...`）には使えない

### ❌ アプローチ 2: `String.intercalate` の展開 + `String.splitOn` の回避

```lean
-- ofString? を自前の splitOnColon に置き換えて String.splitOn を排除
-- しかし toString 側は String.intercalate をそのまま使用
```

**失敗理由**:
- `String.intercalate` は1段階は `unfold` できるが、内部の `String.intercalate.go` がハイジェニックな名前 `go✝` を持つ
- `go✝` は `simp` / `unfold` / `rfl` いずれでも展開不可能
- そのため `(String.intercalate ":" [a, b]).toList` を `a.toList ++ [':'] ++ b.toList` に書き換えるヘルパー定理が証明できない

```lean
-- このような定理が証明できない:
theorem toString_toList_double (l1 l2 : Layer) :
    (Shape.double l1 l2).toString.toList =
        l1.toString.toList ++ [':'] ++ l2.toString.toList := by
    unfold Shape.toString; unfold String.intercalate
    simp [layers, String.toList_append]
    -- ❌ ゴールに String.intercalate.go✝ が残る
```

### ❌ アプローチ 3: `List.mapM` を使った `ofString?`

```lean
-- splitOnColon の結果を List.mapM で一括変換
def ofString? (s : String) : Option Shape :=
    let parts := splitOnColon s.toList
    match parts.mapM (fun cs => Layer.ofString? (String.ofList cs)) with
    | some [l1]             => some (single l1)
    | some [l1, l2]         => some (double l1 l2)
    ...
```

**失敗理由**:
- `List.mapM` は内部で `List.mapM.loop`（accumulator + `List.reverse` パターン）を使う
- `simp [List.mapM, List.mapM.loop]` で展開すると `do` / `pure` / `.reverse` の形になり、元のパターンマッチと合致しない
- `simp only [List.mapM]` だけでは `List.mapM.loop` の個別ステップまで展開されず、ゴールに `List.mapM.loop ... [] ` が残る

---

## ✅ 成功したアプローチ: `List Char` レベルでの完全自前実装

### 設計原則

**`String` カーネル関数への依存を排除し、`List Char` レベルで全操作を定義する。**

`String` と `List Char` のブリッジには以下の stdlib 補題のみを使う:
- `String.toList_ofList : (String.ofList l).toList = l`
- `String.ofList_toList : String.ofList s.toList = s`

### 実装パターン

#### 1. `toString` を `toCharList` + `String.ofList` の二段構成にする

```lean
-- ❌ String.intercalate を使う（展開不可能）
protected def toString (s : Shape) : String :=
    ":".intercalate (s.layers.map Layer.toString)

-- ✅ List Char レベルで定義し、String.ofList でラップ
def toCharList : Shape → List Char
    | single l1 => l1.toString.toList
    | double l1 l2 =>
        l1.toString.toList ++ ':' :: l2.toString.toList
    | triple l1 l2 l3 =>
        l1.toString.toList ++ ':' :: (l2.toString.toList ++ ':' :: l3.toString.toList)
    | quadruple l1 l2 l3 l4 =>
        l1.toString.toList ++ ':' :: (l2.toString.toList ++ ':' ::
        (l3.toString.toList ++ ':' :: l4.toString.toList))

protected def toString (s : Shape) : String :=
    String.ofList s.toCharList
```

**重要**: `toCharList` の区切り文字は `[':'] ++ ...` ではなく `':' :: ...` で書く。
- `[':'] ++ rest` は `List.cons ':' List.nil ++ rest` に展開され、`splitOnColon_append_colon` の `l1 ++ ':' :: l2` パターンとマッチしない
- `':' :: rest` は直接 `List.cons ':' rest` なので即座にマッチする

#### 2. `ofString?` で `splitOn` / `mapM` を排除し、自前 `splitOnColon` + 直接パターンマッチ

```lean
-- 自前の split 関数
private def splitOnColon : List Char → List (List Char)
    | [] => [[]]
    | c :: rest =>
        if c == ':' then [] :: splitOnColon rest
        else match splitOnColon rest with
             | [] => [[c]]
             | hd :: tl => (c :: hd) :: tl

-- mapM を使わず splitOnColon の結果を直接パターンマッチ
def ofString? (s : String) : Option Shape :=
    match splitOnColon s.toList with
    | [c1] =>
        match Layer.ofString? (String.ofList c1) with
        | some l1 => some (single l1)
        | none => none
    | [c1, c2] =>
        match Layer.ofString? (String.ofList c1),
              Layer.ofString? (String.ofList c2) with
        | some l1, some l2 => some (double l1 l2)
        | _, _ => none
    ...
```

#### 3. 証明に必要な補助定理チェーン

```
Quarter.toString_noColon  -- 各 Quarter の toString に ':' が含まれないこと
        ↓
Layer.toString_noColon    -- 各 Layer の toString に ':' が含まれないこと
        ↓
splitOnColon_noColon      -- ':' を含まないリスト → [cs]　（末端レイヤの復元）
splitOnColon_append_colon -- l1 ++ ':' :: l2     → l1 :: splitOnColon l2　（分割の復元）
        ↓
Layer.ofString_ofList_toString  -- String 経由でも元に戻ること
        ↓
Shape.ofString_toString   -- 本定理
```

#### 4. 本定理の証明パターン

各ケース共通の **2ステップパターン**:

```lean
theorem ofString_toString (s : Shape) : ofString? s.toString = some s := by
    simp only [ofString?, Shape.toString, String.toList_ofList]
    cases s with
    | double l1 l2 =>
        -- ステップ1: splitOnColon を簡約（rw で左から順にリライト）
        rw [toCharList,
            splitOnColon_append_colon _ _ (Layer.toString_noColon l1),
            splitOnColon_noColon _ (Layer.toString_noColon l2)]
        -- ステップ2: Layer.ofString? を簡約（simp only で一気に解決）
        simp only [Layer.ofString_ofList_toString]
    ...
```

- **ステップ 1** (`rw`): `toCharList` を展開 → `splitOnColon_append_colon` で `:` 区切り部分を分解 → 最後のパートに `splitOnColon_noColon` を適用
- **ステップ 2** (`simp only`): 分解された各パートに `Layer.ofString_ofList_toString` を適用し、`match` を解決

`rw` と `simp only` の使い分けがポイント:
- `rw` は `splitOnColon` の形を段階的にリライトするのに向いている（適用順序を制御可能）
- `simp only` は `match` 式の中の複数の `Layer.ofString?` 呼び出しを一括で解決するのに向いている（パターンが散在していても全て見つける）

---

## 汎用的な教訓

| 問題 | 回避策 |
|---|---|
| `String.splitOn` は `@[irreducible]` で展開不可 | 自前の `List Char` ベース split 関数を定義 |
| `String.intercalate` の内部 `go✝` が展開不可 | `toCharList : T → List Char` を定義し `toString = String.ofList ∘ toCharList` |
| `List.mapM` が `do`/`pure`/`.reverse` に展開される | `mapM` を排除し、split 結果の直接パターンマッチに変更 |
| `[':'] ++ rest` と `':' :: rest` の不一致 | 区切り文字は必ず `':' :: rest` 形式で書く |
| `String` ↔ `List Char` のブリッジ | `String.toList_ofList` / `String.ofList_toList` のみ使用 |

---

## 参考: 使用した stdlib 補題

| 補題 | 内容 |
|---|---|
| `String.toList_ofList` | `(String.ofList l).toList = l` |
| `String.ofList_toList` | `String.ofList s.toList = s` |
| `String.toList_append` | `(s₁ ++ s₂).toList = s₁.toList ++ s₂.toList` |
| `List.mem_append` | `x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂` |
| `beq_iff_eq` | `BEq` を `=` に変換（`if c == ':'` を `if c = ':'` に） |

## 参考: 実装ファイル

| ファイル | 関連する定理 |
|---|---|
| `S2IL/Shape/Quarter.lean` | `Quarter.ofString_toString` |
| `S2IL/Shape/Layer.lean` | `Layer.ofString_toString` |
| `S2IL/Shape/Shape.lean` | `Shape.ofString_toString`（本ドキュメントの主題） |
