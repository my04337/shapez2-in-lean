# Functional Programming in Lean — エージェント向け包括ガイド

> **出典**: [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
> 本ドキュメントは上記書籍の主要概念をエージェントが Lean 4 コードを理解・生成する際の手引きとして要約したものです。

---

## 目次

1. [式と評価](#1-式と評価)
2. [型システム](#2-型システム)
3. [関数と定義](#3-関数と定義)
4. [構造体 (Structure)](#4-構造体-structure)
5. [帰納型とパターンマッチ](#5-帰納型とパターンマッチ)
6. [多相性 (Polymorphism)](#6-多相性-polymorphism)
7. [便利な構文機能](#7-便利な構文機能)
8. [IO と副作用](#8-io-と副作用)
9. [命題・証明・タクティク](#9-命題証明タクティク)
10. [型クラス (Type Classes)](#10-型クラス-type-classes)
11. [モナド (Monads)](#11-モナド-monads)
12. [組み込み型チートシート](#12-組み込み型チートシート)
13. [ベストプラクティス](#13-ベストプラクティス)

---

## 1. 式と評価

Lean 4 は**式指向言語**であり、プログラムは数学的な式の評価としてモデル化される。

### コマンド

| コマンド | 用途 | 例 |
|---|---|---|
| `#eval` | 式を評価して結果を表示 | `#eval 1 + 2` → `3` |
| `#check` | 式の型を表示（評価はしない） | `#check (1 + 2 : Nat)` → `1 + 2 : Nat` |

### 式の評価モデル

- 関数適用はスペースで行う: `f x` （括弧方式 `f(x)` ではない）
- 関数適用は**左結合**: `f a b` は `(f a) b`
- 算術演算子の優先順位は通常の数学と同じ
- 式の評価は副作用を持たない純粋な計算

```lean
#eval String.append "Hello, " "Lean!"  -- "Hello, Lean!"
#eval if 1 > 2 then "yes" else "no"     -- "no"
```

---

## 2. 型システム

Lean の型システムはすべての式に対して型を保証する。型の不一致はコンパイル時にエラーとなる。

### 基本型

| 型 | 説明 | リテラル例 |
|---|---|---|
| `Nat` | 自然数（0以上の整数、任意精度） | `0`, `42`, `1000000` |
| `Int` | 整数（正負） | `-5`, `0`, `42` |
| `Float` | 浮動小数点数 | `3.14`, `-0.5` |
| `String` | 文字列 | `"hello"` |
| `Char` | 文字 | `'a'`, `'λ'` |
| `Bool` | 真偽値 | `true`, `false` |
| `Unit` | 単位型（情報なし、C の void に相当） | `()` |

### 型注釈

```lean
-- 型注釈は式の後に `:` で付ける
#check (42 : Int)         -- 42 : Int （デフォルトは Nat）
def x : Float := 1.5
```

### 型推論

- Lean は多くの場合、型を自動推論できる
- 数値リテラルはデフォルトで `Nat` に推論される
- 関数の引数型は通常、明示的な注釈が必要
- 推論に失敗した場合 "failed to infer" やメタ変数 `?m.XYZ` エラーが出る
- **ベストプラクティス**: 型注釈は多めに書く方が良い（可読性・エラー特定・仕様としての役割）

---

## 3. 関数と定義

### `def` による定義

```lean
def double (n : Nat) : Nat := n + n

-- 型注釈付き（推奨）
def add (a : Nat) (b : Nat) : Nat := a + b

-- 関数は自動的にカリー化される
#check add       -- add : Nat → Nat → Nat
#eval add 3 5    -- 8
```

### `abbrev` vs `def`

- `def`: 通常の定義。タクティクや型クラス推論で**自動展開されない**
- `abbrev`: 略語定義。自動展開の対象となり、`simp` や `decide` タクティクで利用可能

```lean
def MyNat := Nat           -- simp/decide で展開されない
abbrev MyNat' := Nat       -- simp/decide で展開される
```

### 関数型

```lean
-- 関数型は `→` で表記
-- A → B → C は A → (B → C) と同じ（右結合）
def greet : String → String := fun name => s!"Hello, {name}!"
```

---

## 4. 構造体 (Structure)

構造体は名前付きフィールドを持つデータ型。

### 定義

```lean
structure Point where
    x : Float
    y : Float
deriving Repr
```

### 構築方法

```lean
-- 方法1: コンストラクタ直接呼び出し
def p1 := Point.mk 1.0 2.0

-- 方法2: ブレース記法（名前付き）
def p2 : Point := { x := 1.0, y := 2.0 }

-- 方法3: アングルブラケット記法（位置引数）
def p3 : Point := ⟨1.0, 2.0⟩
```

### フィールドアクセスとドット記法

```lean
#eval p1.x          -- 1.0
#eval p1.y          -- 2.0

-- ドット記法: 型名を名前空間として関数を呼び出す
def Point.distanceToOrigin (p : Point) : Float :=
    Float.sqrt (p.x * p.x + p.y * p.y)

#eval p1.distanceToOrigin   -- ドット記法で呼び出し
```

### 更新構文

```lean
-- `with` を使って一部のフィールドだけ変更したコピーを作成
def p4 : Point := { p1 with y := 5.0 }
-- p4 = { x := 1.0, y := 5.0 }
```

---

## 5. 帰納型とパターンマッチ

### `inductive` による帰納型定義

```lean
-- Bool の定義（標準ライブラリ）
inductive Bool where
    | false : Bool
    | true : Bool

-- Nat の定義（ペアノ自然数、標準ライブラリ）
inductive Nat where
    | zero : Nat
    | succ (n : Nat) : Nat
```

### パターンマッチ

```lean
-- match 式
def isZero (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ _ => false

-- パターンマッチ定義（直接ケースを書く）
def isZero' : Nat → Bool
    | 0 => true
    | _ + 1 => false
```

### 再帰関数

```lean
def factorial : Nat → Nat
    | 0 => 1
    | n + 1 => (n + 1) * factorial n
```

### 停止性検査

- Lean は**構造的再帰** (structural recursion) を自動検出し、停止性を検証する
- 引数の構造的に小さい部分に対して再帰呼び出しする必要がある
- 停止性を証明できない場合は `termination_by` で減少する指標を指定する
- **同時マッチ** (`match xs, ys with`) はペアでのマッチ (`match (xs, ys) with`) より停止性検査に有利

---

## 6. 多相性 (Polymorphism)

### 型引数

```lean
-- 明示的な型引数
def length {α : Type} (xs : List α) : Nat :=
    match xs with
    | [] => 0
    | _ :: ys => 1 + length ys
```

### 暗黙引数 (Implicit Arguments)

| 記法 | 意味 |
|---|---|
| `{α : Type}` | 暗黙引数。呼び出し側で省略でき、Lean が推論する |
| `(α : Type)` | 明示引数。呼び出し側で必ず指定する |
| `[inst : ToString α]` | インスタンス暗黙引数。型クラスのインスタンスを自動検索する |

```lean
-- 暗黙引数は呼び出し時に省略される
#eval length [1, 2, 3]         -- 3 （α = Nat は自動推論）

-- 明示的に渡したい場合は @ を使う
#eval @length Nat [1, 2, 3]    -- 3
```

### 自動暗黙引数

Lean は未宣言の型変数を自動的に暗黙引数として扱う:

```lean
-- 以下の2つは同じ意味
def length {α : Type} (xs : List α) : Nat := ...
def length (xs : List α) : Nat := ...  -- α は自動的に暗黙引数になる
```

### `deriving Repr`

```lean
-- deriving Repr を付けると #eval で表示可能になる
structure Point where
    x : Float
    y : Float
deriving Repr
```

---

## 7. 便利な構文機能

### パターンマッチ定義

引数名を省略し、直接パターンケースを書ける:

```lean
def length : List α → Nat
    | [] => 0
    | _ :: ys => 1 + length ys

-- 複数引数のパターンをカンマ区切りで書く
def drop : Nat → List α → List α
    | 0, xs => xs
    | _, [] => []
    | n + 1, _ :: xs => drop n xs
```

### ローカル定義 (`let` / `let rec`)

```lean
def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
        let (xs, ys) := unzip xys   -- let でパターン分解
        (x :: xs, y :: ys)

-- 再帰的ローカル定義には let rec を使う
def reverse (xs : List α) : List α :=
    let rec helper : List α → List α → List α
        | [], soFar => soFar
        | y :: ys, soFar => helper ys (y :: soFar)
    helper xs []
```

### 無名関数 (Lambda)

```lean
-- fun キーワード
#eval (fun x => x + 1) 5                -- 6
#eval (fun (x : Int) => x + 1) 5        -- 6（型注釈付き）

-- パターンマッチ付き無名関数
#check fun
    | 0 => none
    | n + 1 => some n

-- 中点 (·) による省略記法
#eval (· + 1) 5        -- 6
#eval (· * 2) 5        -- 10
#eval (· + ·) 3 5      -- 8（複数の · は左から右の引数）
```

### 名前空間 (Namespace)

```lean
namespace MyModule
    def helper (x : Nat) := x + 1
end MyModule

#eval MyModule.helper 5    -- 6

-- open で名前空間を開く
open MyModule in
#eval helper 5             -- 6

-- ドット記法: 型名を名前空間として使う
def Nat.double (x : Nat) : Nat := x + x
#eval (4 : Nat).double     -- 8
```

### `if let`

一つのコンストラクタだけに関心がある場合に便利:

```lean
def getString? (inline : Inline) : Option String :=
    if let Inline.string s := inline then
        some s
    else
        none
```

### 自然数パターン

```lean
-- 自然数パターンではリテラルと + が使える
def even : Nat → Bool
    | 0 => true
    | n + 1 => !even n

def halve : Nat → Nat
    | 0 => 0
    | 1 => 0
    | n + 2 => halve n + 1
-- 注意: + の右辺は常にリテラル。n + 2 は OK、2 + n はエラー
```

### 文字列補間

```lean
#eval s!"2 + 3 = {2 + 3}"       -- "2 + 3 = 5"
-- {式} の中に任意の式を埋め込める（ToString インスタンスが必要）
```

### 同時マッチ

```lean
-- カンマ区切りで複数の値を同時にマッチ
def sameLength (xs : List α) (ys : List β) : Bool :=
    match xs, ys with
    | [], [] => true
    | _ :: xs', _ :: ys' => sameLength xs' ys'
    | _, _ => false
-- ペアでマッチするよりも停止性検査に有利
```

---

## 8. IO と副作用

### IO の基本概念

- Lean は純粋関数型言語。副作用は `IO` 型で記述する
- `IO α` は「実行すると型 `α` の値を返す可能性のある副作用付きアクション」の型
- 式の**評価**（純粋）と IO アクションの**実行**（副作用あり）は明確に区別される
- `main : IO Unit` がプログラムのエントリポイント

### `do` 記法

```lean
def main : IO Unit := do
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    stdout.putStrLn "What is your name?"
    let input ← stdin.getLine
    let name := input.dropRightWhile Char.isWhitespace
    stdout.putStrLn s!"Hello, {name}!"
```

### `do` ブロックの構文要素

| 構文 | 意味 |
|---|---|
| `let x ← expr` | IO アクション `expr` を実行し、結果を `x` に束縛 |
| `let x := expr` | 純粋な式を評価し、結果を `x` に束縛（副作用なし） |
| `expr` | IO アクション式を評価して実行（結果は捨てる） |
| `return expr` | 値を返す |
| `pure x` | 副作用なしで値 `x` を返す IO アクション |

### IO アクションは第一級の値

```lean
-- IO アクションを変数に格納し、後で実行できる
def twice (action : IO Unit) : IO Unit := do
    action
    action

-- IO アクションのリストを順に実行
def runActions : List (IO Unit) → IO Unit
    | [] => pure ()
    | act :: actions => do
        act
        runActions actions
```

### 主な IO 関数

| 関数 | 型 | 用途 |
|---|---|---|
| `IO.println` | `String → IO Unit` | 文字列を標準出力に改行付きで表示 |
| `IO.getStdin` | `IO IO.FS.Stream` | 標準入力ストリームを取得 |
| `IO.getStdout` | `IO IO.FS.Stream` | 標準出力ストリームを取得 |
| `IO.FS.Stream.getLine` | `IO.FS.Stream → IO String` | ストリームから1行読み取り |
| `IO.FS.Stream.putStrLn` | `IO.FS.Stream → String → IO Unit` | 文字列を改行付きで書き込み |

---

## 9. 命題・証明・タクティク

### 命題 (Proposition) と証明 (Proof)

- **Propositions as Types**: Lean では命題は型であり、証明はその型の値
- `Prop` は命題の宇宙（`Type` がデータ型の宇宙であるのと同様）
- 真の命題は証拠（値）を構築できる。偽の命題は構築不可能

```lean
-- rfl: 両辺が計算的に等しいことの証明
def onePlusOneIsTwo : 1 + 1 = 2 := rfl

-- theorem: 定理宣言（def と同等だが、証明であることを示す慣例）
theorem addComm : 1 + 1 = 2 := rfl
```

### 論理結合子 (Connectives)

| 論理 | Lean 表記 | 証拠の構築 |
|---|---|---|
| True | `True` | `True.intro` |
| False | `False` | 証拠なし（構築不可能） |
| A かつ B | `A ∧ B` | `And.intro : A → B → A ∧ B` |
| A または B | `A ∨ B` | `Or.inl : A → A ∨ B` または `Or.inr : B → A ∨ B` |
| A ならば B | `A → B` | `A` の証拠を `B` の証拠に変換する関数 |
| A でない | `¬A` | `A → False` と等価 |

### タクティク (Tactics)

タクティクは証明を自動・半自動で構築するプログラム。`by` で開始する。

| タクティク | 用途 | 例 |
|---|---|---|
| `decide` | 決定手続き（具体値の等式・不等式等） | `theorem t : 1 + 1 = 2 := by decide` |
| `simp` | 簡約（書き換え規則の自動適用） | `theorem t : ... := by simp` |
| `grind` | SMT 風の自動証明（成功か失敗のみ） | `theorem t : ... := by grind` |
| `rfl` | 反射性（計算的に等しいことの証明） | `theorem t : 1 + 1 = 2 := by rfl` |

### 配列・リストの安全なインデックスアクセス

```lean
-- コンパイル時に境界チェック（デフォルト）
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- 実行時チェック（パニック）
#eval woodlandCritters[1]!

-- Option を返す
#eval woodlandCritters[5]?    -- none

-- 証明を渡す
#eval third myList (by decide)
```

---

## 10. 型クラス (Type Classes)

### 概要

型クラスは**関数のオーバーロード**のための仕組み。他言語のインターフェース/トレイトに相当。

### 定義と実装

```lean
-- クラス定義
class ToString (α : Type) where
    toString : α → String

-- インスタンス定義
instance : ToString Point where
    toString p := s!"({p.x}, {p.y})"
```

### 主要な標準型クラス

| 型クラス | 用途 | 主なメソッド |
|---|---|---|
| `Add` | 加算 `+` | `add : α → α → α` |
| `Sub` | 減算 `-` | `sub : α → α → α` |
| `Mul` | 乗算 `*` | `mul : α → α → α` |
| `Div` | 除算 `/` | `div : α → α → α` |
| `Neg` | 単項マイナス `-` | `neg : α → α` |
| `BEq` | 等値比較 `==` | `beq : α → α → Bool` |
| `Ord` | 順序比較 | `compare : α → α → Ordering` |
| `ToString` | 文字列変換 | `toString : α → String` |
| `Repr` | 表示用変換（`#eval`で使用） | `reprPrec : α → Nat → Std.Format` |
| `Inhabited` | デフォルト値あり | `default : α` |
| `Hashable` | ハッシュ計算 | `hash : α → UInt64` |
| `DecidableEq` | 等値の決定可能性 | 命題レベルの等値判定 |

### `deriving` による自動導出

```lean
structure Color where
    r : Nat
    g : Nat
    b : Nat
deriving Repr, BEq, Hashable, Inhabited
```

### インスタンス暗黙引数

```lean
-- [ToString α] はインスタンス暗黙引数
def showList [ToString α] (xs : List α) : String :=
    xs.map toString |>.toString
```

---

## 11. モナド (Monads)

### 概要

モナドは**連鎖可能な計算パターン**を抽象化する。以下のようなパターンをまとめて扱う:

- `Option`: null チェックの連鎖
- `Except`: 例外処理の連鎖
- `IO`: 副作用のある操作の連鎖
- `List`: 非決定的計算

### `do` 記法とモナド

`do` 記法は `IO` だけでなく、任意のモナドで使える:

```lean
-- Option モナドでの do 記法
def safeDivide (x y : Nat) : Option Nat :=
    if y == 0 then none else some (x / y)

def compute : Option Nat := do
    let a ← safeDivide 10 2
    let b ← safeDivide a 0    -- none が返るとここで早期リターン
    pure (a + b)
```

### Monad 型クラス

```lean
class Monad (m : Type → Type) extends Bind m, Pure m where
    -- bind : m α → (α → m β) → m β
    -- pure : α → m α
```

- `pure x`: 値 `x` を持つ最小の計算を作る
- `bind ma f` (または `ma >>= f`): 計算 `ma` の結果に `f` を適用
- `do` 記法は `bind` と `pure` のシンタックスシュガー

---

## 12. 組み込み型チートシート

### `Option α`

```lean
inductive Option (α : Type) where
    | none : Option α
    | some (val : α) : Option α

-- 使用例
def find? (xs : List Nat) (pred : Nat → Bool) : Option Nat :=
    match xs with
    | [] => none
    | x :: xs => if pred x then some x else find? xs pred
```

### `List α`

```lean
-- リテラル記法
def xs : List Nat := [1, 2, 3]

-- コンストラクタ
-- [] は空リスト、x :: xs は先頭に追加

-- 主なメソッド
#eval [1, 2, 3].length       -- 3
#eval [1, 2, 3].map (· * 2)  -- [2, 4, 6]
#eval [1, 2, 3].filter (· > 1)  -- [2, 3]
#eval [1, 2, 3].reverse      -- [3, 2, 1]
#eval [1, 2] ++ [3, 4]       -- [1, 2, 3, 4]
```

### `Prod α β`（ペア / タプル）

```lean
-- Prod α β は α × β と書ける
def pair : Nat × String := (42, "hello")
#eval pair.fst    -- 42
#eval pair.snd    -- "hello"

-- 入れ子: α × β × γ は α × (β × γ)
```

### `Sum α β`

```lean
inductive Sum (α β : Type) where
    | inl (val : α) : Sum α β
    | inr (val : β) : Sum α β
-- Either 型に相当
```

### `Unit` と `Empty`

```lean
-- Unit: 値が1つだけの型（情報なし）
-- Empty: 値が存在しない型（不可能を表す）
```

---

## 13. ベストプラクティス

### 型注釈

- トップレベル定義には常に型シグネチャを書く
- ローカル変数はコンテキストから推論できる場合は省略してもよい
- 引数には型注釈を付ける（推論失敗を防ぐ）

### パターンマッチ

- 同時マッチ `match x, y with` はペアマッチ `match (x, y) with` より推奨（停止性検査のため）
- ワイルドカード `_` で不要なパターンを無視する
- 自然数パターン `n + 1` を活用する（`Nat.succ n` の代わり）

### 命名規則（S2IL プロジェクト準拠）

- 型・構造体・クラス・帰納型: `UpperCamelCase`
- 定理・補題: `lowerCamelCase`
- 関数・定義: `lowerCamelCase`
- 名前空間: `UpperCamelCase`
- `Prop` を返す述語: `is` / `has` 接頭辞（例: `isEven`）

### 停止性

- 構造的再帰を優先する
- 停止性が自明でない場合は `termination_by` を明示する
- `decreasing_by` で減少の証明を提供する

### `def` vs `abbrev` vs `theorem`

| キーワード | 用途 | タクティクでの展開 |
|---|---|---|
| `def` | 関数・値の定義 | 展開されない |
| `abbrev` | 略語・エイリアス | 自動展開される |
| `theorem` | 定理の証明 | 証明の詳細は参照されない |

### IO プログラミング

- `do` ブロック内で `←` は IO アクションの実行・束縛に使う
- `:=` は純粋な式の束縛に使う
- `pure ()` は副作用のない空アクション
- IO アクションは第一級の値として扱える（遅延実行可能）

### エラーメッセージの読み方

| メッセージ | 原因 | 対処 |
|---|---|---|
| "failed to infer" | 型推論の失敗 | 型注釈を追加する |
| メタ変数 `?m.XYZ` | 未決定の型 | 明示的な型を指定する |
| "failed to synthesize instance" | 型クラスインスタンスが見つからない | インスタンスを定義するか `deriving` を追加 |
| "failed to prove index is valid" | 配列インデックスの境界証明不足 | `by decide`、`[i]!`、`[i]?` を使う |
| "fail to show termination" | 停止性の証明不足 | `termination_by` を追加する |

---

## 免責事項

本ドキュメントは非公式の解説・要約資料です。Lean プロジェクトおよびその著者（David Thrane Christiansen 氏）とは一切関係がありません。内容の正確さについて一切保証しません。本ドキュメントを参照したことによって生じたいかなる損害についても、作成者は責任を負いません。

## ライセンス・著作権表記

本ドキュメントは以下の著作物を要約・再編集した派生物であり、Apache License 2.0 に基づいて頒布されます。

**原著作物:**

- 書名: *Functional Programming in Lean*
- 著作権者: Copyright David Thrane Christiansen
- ライセンス: Apache License 2.0
- リポジトリ: <https://github.com/leanprover/functional_programming_in_lean>
- 公開 URL: <https://lean-lang.org/functional_programming_in_lean/>

本ドキュメントは原著作物を要約・再構成・注解・翻訳したものです。Apache License 2.0 の全文は <https://www.apache.org/licenses/LICENSE-2.0> を参照してください。
