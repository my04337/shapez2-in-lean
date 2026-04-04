# Theorem Proving in Lean 4 — エージェント向け定理証明ガイド

> **出典**: [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)（Jeremy Avigad, Leonardo de Moura, Soonho Kong, Sebastian Ullrich 著）
> Lean バージョン: 4.26.0

本ドキュメントは、Lean 4 で定理証明を行うエージェントが知るべき重要概念・テクニック・ベストプラクティスを一つにまとめたガイドです。

---

## 目次

1. [依存型理論の基礎](#1-依存型理論の基礎)
2. [命題と証明](#2-命題と証明)
3. [量化子と等式](#3-量化子と等式)
4. [タクティク](#4-タクティク)
5. [Lean との対話](#5-lean-との対話)
6. [帰納型](#6-帰納型)
7. [帰納と再帰](#7-帰納と再帰)
8. [構造体とレコード](#8-構造体とレコード)
9. [型クラス](#9-型クラス)
10. [変換タクティクモード (conv)](#10-変換タクティクモード-conv)
11. [公理と計算](#11-公理と計算)
12. [タクティク早見表](#12-タクティク早見表)
13. [ベストプラクティス総括](#13-ベストプラクティス総括)

---

## 1. 依存型理論の基礎

Lean は **Calculus of Constructions** に基づく依存型理論の上に構築されている。全ての式は型を持ち、型自体も型を持つ。

### 1.1 型と項

```lean
-- 基本的な型と値
def m : Nat := 1
def b : Bool := true

-- 型検査と評価
#check m            -- m : Nat
#check Nat → Nat    -- Nat → Nat : Type
#eval m + 2         -- 3
```

### 1.2 宇宙階層

型の型は `Type`、`Type` の型は `Type 1`、以下無限に続く。`Type` は `Type 0` の略記。

```lean
#check Type     -- Type : Type 1
#check Type 1   -- Type 1 : Type 2
#check Type 2   -- Type 2 : Type 3
```

宇宙多相には `universe` コマンドを使う:

```lean
universe u
def F (α : Type u) : Type u := Prod α α
#check F   -- F.{u} (α : Type u) : Type u
```

### 1.3 関数型とラムダ抽象

関数は `fun`（= `λ`）で作り、適用するだけ。引数は空白で区切る（カリー化）。

```lean
#check fun (x : Nat) => x + 5     -- Nat → Nat
#eval (fun x : Nat => x + 5) 10   -- 15

-- 複数引数のラムダ
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x * 2
```

`→` は右結合: `Nat → Nat → Nat` は `Nat → (Nat → Nat)` と同じ。

### 1.4 定義

`def` はラムダ抽象に名前を付ける:

```lean
def double (x : Nat) : Nat := x + x
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
```

### 1.5 ローカル定義 (let)

`let` はスコープ内で名前を束縛する。`fun` と異なり、束縛先の値を直接参照できる:

```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

### 1.6 variable と section

`variable` で繰り返し使う引数を自動挿入させ、`section` でスコープを制限する:

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β)

  def compose := fun x => g (f x)
  -- 自動的に α β γ g f が引数に挿入される
end useful
```

### 1.7 名前空間

`namespace` で定義を階層化し、`open` で短縮名を利用:

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7
end Foo

open Foo
#eval f a   -- 12
```

### 1.8 依存関数型

型が引数に依存する関数型 `(a : α) → β a`。`List α` の `cons` が典型例:

```lean
def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as
-- cons Nat : Nat → List Nat → List Nat
-- cons Bool : Bool → List Bool → List Bool
```

### 1.9 暗黙引数

`{}` で囲むと Lean が自動推論する暗黙引数になる。`@` で明示的に渡せる:

```lean
def ident {α : Type} (x : α) := x

#check ident 1        -- Nat（αは自動推論）
#check @ident Nat 1   -- 明示的にNatを渡す
```

---

## 2. 命題と証明

### 2.1 Curry-Howard 同型

Lean では **命題 = 型、証明 = 項** という対応（Curry-Howard 同型）が成り立つ。`Prop` は命題の宇宙（`Sort 0`）。

```lean
-- 命題 p の証明とは、型 p の項を構成すること
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

-- 含意 p → q の証明は、p の証明を受け取り q の証明を返す関数
theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p => h₁ (h₂ h₃)
```

### 2.2 論理結合子

| 結合子 | 型 | 構成 | 分解 |
|---|---|---|---|
| `∧` (And) | `Prop → Prop → Prop` | `And.intro h₁ h₂` / `⟨h₁, h₂⟩` | `.left` / `.right` |
| `∨` (Or) | `Prop → Prop → Prop` | `Or.inl h` / `Or.inr h` | `Or.elim h f g` |
| `¬` (Not) | `Prop → Prop` | `fun h => ...` (`¬p = p → False`) | 関数適用 |
| `↔` (Iff) | `Prop → Prop → Prop` | `Iff.intro f g` | `.mp` / `.mpr` |

```lean
-- And
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

-- Or
example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

-- Not
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp => hnq (hpq hp)

-- Iff
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro (fun h => ⟨h.right, h.left⟩) (fun h => ⟨h.right, h.left⟩)
```

### 2.3 have / show / suffices

証明内で補助的な事実に名前を付ける:

```lean
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from h.right
```

### 2.4 古典論理

`open Classical` で排中律 `em`、`byContradiction`、`byCases` が使える:

```lean
open Classical

-- 二重否定除去
example (h : ¬¬p) : p :=
  byCases (fun h1 : p => h1) (fun h1 : ¬p => absurd h1 h)

-- 排中律
#check @Classical.em  -- ∀ (p : Prop), p ∨ ¬p
```

---

## 3. 量化子と等式

### 3.1 全称量化 (∀)

`∀ x : α, p x` は依存関数型 `(x : α) → p x` と同一。`fun` で導入し、適用で除去:

```lean
example (α : Type) (p q : α → Prop) :
    (∀ x, p x ∧ q x) → ∀ y, p y :=
  fun h y => (h y).left
```

### 3.2 等式 (Eq)

| 技法 | 説明 |
|---|---|
| `rfl` | 反射律。定義的等価な式に使用 |
| `Eq.symm` | `a = b → b = a` |
| `Eq.trans` | `a = b → b = c → a = c` |
| `congrArg f h` | `a = b → f a = f b` |
| `congrFun h a` | `f = g → f a = g a` |
| `Eq.subst` | `a = b → p a → p b` |

```lean
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (hab : a = b) (hbc : b = c) : a = c := hab.trans hbc
```

### 3.3 calc ブロック

等式（や不等式）の連鎖を可読に記述する:

```lean
example (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) : a = d + 1 :=
  calc a = b     := h1
    _ = c + 1    := h2
    _ = d + 1    := congrArg (· + 1) h3
```

`rw` や `simp` と組み合わせると強力:

```lean
example (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) :
    a = e := by
  simp [h1, h2, h3, Nat.add_comm, h4]
```

### 3.4 rw タクティク

等式でゴールを書き換える:

```lean
example (h : a = b) : a + c = b + c := by rw [h]
example (h : a = b) : b + c = a + c := by rw [← h]   -- 逆方向
example (h1 : a = b) (h2 : b = c) : a = c := by rw [h1, h2]  -- 複数
```

### 3.5 存在量化 (∃)

`∃ x, p x` の証明には具体的な証拠（witness）を提示する:

```lean
-- 構成
example : ∃ x : Nat, x > 0 := ⟨1, Nat.lt.base 0⟩

-- 分解
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

---

## 4. タクティク

### 4.1 タクティクモード

`by` キーワードで項モードからタクティクモードに入る。タクティクは **ゴール** を変形して証明を構築する:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp
```

### 4.2 主要タクティク一覧

| タクティク | 用途 |
|---|---|
| `apply t` | ゴールに定理/関数を適用。未解決の引数がサブゴールになる |
| `exact t` | ゴールを正確に満たす項を提供して証明完了 |
| `intro x` | `∀` や `→` の仮定をコンテキストに導入 |
| `constructor` | ゴール型のコンストラクタを適用（`And.intro` / `Exists.intro` 等） |
| `cases h` | 帰納型の仮定 `h` を場合分け |
| `induction x` | `x` に関する帰納法 |
| `assumption` | コンテキストからゴールに合う仮定を自動検索 |
| `contradiction` | コンテキスト中の矛盾を検出 |
| `have h : T := ...` | 補助的な事実を導入 |
| `show T` | ゴールの型を明示 |
| `rw [h₁, h₂, ← h₃]` | 等式による書き換え |
| `simp [h₁, h₂, ...]` | 登録済みルール + 指定補題で自動簡約 |
| `simp [*]` | コンテキストの全仮定も利用 |
| `omega` | 線形算術（Nat / Int の等式・不等式）を自動解決 |
| `ring` | 可換環の等式を自動解決 |
| `rfl` | 反射律 `x = x`（定義的等価含む） |
| `decide` | `Decidable` インスタンスで簡単なゴールを自動証明 |
| `exists t` | 存在量化子のゴールに witness を提供 |

### 4.3 cases と induction

```lean
-- 場合分け
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- 帰納法
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
```

### 4.4 タクティクコンビネータ

```lean
-- <;> : 全サブゴールに同じタクティクを適用
example : p ∧ q → q ∧ p := by
  intro h; cases h with
  | intro hp hq => constructor <;> assumption

-- first | t₁ | t₂ : 最初に成功するものを試す
```

### 4.5 項モードとタクティクモードの混合

両者は自由に組み合わせられる:

```lean
-- タクティク内で項を直接使う
example (hp : p) (hq : q) : p ∧ q := by exact ⟨hp, hq⟩

-- 項内でタクティクを使う
example (hp : p) (hq : q) : p ∧ q := ⟨hp, by exact hq⟩
```

### 4.6 タクティクと項による証明の使い分け

| 場面 | 推奨 |
|---|---|
| 短く直接的な証明、単純な論理式 | 項による証明 |
| 複雑な場合分け、書き換えの連鎖 | タクティク |
| 自動化が効く場合（`simp`, `omega`, `ring`） | タクティク |
| コンビネータ的な構成 | 項による証明 |

---

## 5. Lean との対話

### 5.1 対話コマンド

| コマンド | 用途 |
|---|---|
| `#check e` | 式 `e` の型を表示 |
| `#check @e` | 暗黙引数を含む完全な型を表示 |
| `#eval e` | 式を評価して結果を表示（コンパイル済みコード使用、高速） |
| `#reduce e` | カーネルレベルで簡約（遅いが内部構造を観察可能） |
| `#print n` | 定義 `n` の内部表現を表示 |
| `#guard_msgs in cmd` | コマンドのメッセージを検証 |

### 5.2 set_option

```lean
set_option pp.all true          -- 全情報を表示（デバッグ時に有用）
set_option pp.explicit true     -- 暗黙引数を明示
set_option autoImplicit false   -- 自動暗黙引数を無効化（推奨）
```

### 5.3 open の詳細

```lean
open Nat (succ zero gcd)         -- 特定の名前だけ開く
open Nat hiding succ gcd         -- 特定の名前を除外
open Nat renaming mul → times    -- リネーム
```

### 5.4 暗黙引数の種類

| 構文 | 種類 | 説明 |
|---|---|---|
| `(x : α)` | 明示的 | 必ず渡す |
| `{x : α}` | 暗黙 | Lean が推論 |
| `{{x : α}}` | 厳格暗黙（strict implicit） | 明示的引数が与えられるまで展開しない |
| `[x : α]` | インスタンス暗黙 | 型クラス推論で解決 |

### 5.5 autoImplicit

宣言されていない変数を自動的に暗黙引数にする機能。タイポが暗黙変数になるリスクがあるため、**プロダクションコードでは `set_option autoImplicit false` を推奨**。

---

## 6. 帰納型

### 6.1 基本パターン

Lean の具象型はすべて帰納型として定義される:

```lean
-- 列挙型
inductive Weekday where
  | sunday | monday | tuesday | wednesday | thursday | friday | saturday

-- パラメータ付き型
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

-- 再帰型
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α
```

### 6.2 命題としての帰納型

論理結合子は帰納型として定義されている:

| 命題 | 定義 | 意味 |
|---|---|---|
| `True` | コンストラクタ `intro` 1つ | 自明に証明可能 |
| `False` | コンストラクタなし | 証明不可能 |
| `And p q` | `intro : p → q → And p q` | 論理積 |
| `Or p q` | `inl : p → Or p q` / `inr : q → Or p q` | 論理和 |
| `Exists p` | `intro : (w : α) → p w → Exists p` | 存在量化 |

### 6.3 帰納族（Inductive Families）

インデックス付きの型の族。型レベルの制約をエンコードする:

```lean
inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
```

### 6.4 パラメータとインデックスの区別

コロン `:` の前がパラメータ（全コンストラクタで固定）、後がインデックス（コンストラクタごとに変化）:

```lean
inductive Foo (α : Type) : Nat → Type where  -- α はパラメータ、Nat はインデックス
  | mk : α → Foo α 0
```

### 6.5 相互帰納型

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

---

## 7. 帰納と再帰

### 7.1 パターンマッチ

等式コンパイラにより、パターンマッチはプリミティブな recursor にコンパイルされる:

```lean
def isZero : Nat → Bool
  | 0     => true
  | _ + 1 => false

-- 定義方程式は定義的に成り立つ
example : isZero 0 = true := rfl
```

### 7.2 構造的再帰

引数のサブタームに対する再帰呼び出し:

```lean
def add : Nat → Nat → Nat
  | m, 0     => m
  | m, n + 1 => (add m n) + 1

def length : List α → Nat
  | []      => 0
  | _ :: as => length as + 1
```

### 7.3 Well-Founded Recursion

構造的再帰が使えない場合、整礎関係による停止性証明で正当化する:

```lean
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
```

**`termination_by`** で停止性の量を指定:

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y + 1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)    -- 辞書式順序
```

> Lean はまず構造的再帰を試み、失敗した場合のみ well-founded recursion にフォールバックする。

### 7.4 ローカル再帰 (where / let rec)

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   acc => acc
    | n+1, acc => loop n (a :: acc)
```

### 7.5 相互再帰

```lean
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n
  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end
```

### 7.6 依存パターンマッチ

インデックス付き帰納型でパターン内の値が型の制約により強制される:

```lean
def Vect.zipWith (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (zipWith f as bs)
```

---

## 8. 構造体とレコード

### 8.1 structure コマンド

単一コンストラクタの帰納型。射影関数が自動生成される:

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr
```

### 8.2 オブジェクト生成と更新

```lean
def p : Point Nat := { x := 1, y := 2 }
def q := { p with y := 3 }   -- { x := 1, y := 3 }
```

### 8.3 ドット記法

`p.x` は `Point.x p` の略記:

```lean
def Point.add (p q : Point Nat) := Point.mk (p.x + q.x) (p.y + q.y)
#eval p.add q
```

### 8.4 構造体の継承 (extends)

```lean
structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

---

## 9. 型クラス

### 9.1 定義と instance

```lean
class Add (α : Type) where
  add : α → α → α

instance : Add Nat where
  add := Nat.add
```

### 9.2 インスタンス暗黙引数 `[...]`

`[Add α]` と書くと、Lean の型クラス推論が自動で適切なインスタンスを解決する:

```lean
def double [Add α] (x : α) := Add.add x x
```

### 9.3 インスタンス連鎖

既存インスタンスを組み合わせて新しいインスタンスを合成:

```lean
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)
```

### 9.4 outParam（出力パラメータ）

入力パラメータから出力パラメータを決定させる:

```lean
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ
```

### 9.5 Decidable と型クラス

`if-then-else` は `[Decidable c]` インスタンスが必要:

```lean
-- decide タクティクは Decidable インスタンスで自動証明
example : 10 * 20 = 200 := by decide
```

### 9.6 local / scoped インスタンス

```lean
local instance : Add Nat where add := Nat.add    -- セクション内限定
scoped instance : Add Nat where add := Nat.add   -- open 時のみ有効
```

### 9.7 型強制 (Coercion)

`CoeSort` / `CoeFun` で構造体を型や関数として使用可能にする。

---

## 10. 変換タクティクモード (conv)

`conv` は等式ゴールの **特定の部分式** に潜り込んで書き換えるためのモード。通常の `rw` では書き換え位置を制御できない場面で使う。

### 10.1 基本ナビゲーション

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs          -- 左辺に移動
    congr        -- 各引数にサブゴールを生成
    · rfl        -- 第1引数 a はそのまま
    · rw [Nat.mul_comm]  -- 第2引数 b * c を書き換え
```

| コマンド | 説明 |
|---|---|
| `lhs` / `rhs` | 等式の左辺/右辺に移動 |
| `congr` | ヘッド関数の各引数にサブゴールを生成 |
| `arg i` | i番目の明示的引数に移動 |
| `intro x` | ラムダ式の中に入る |
| `enter [1, x, 2]` | `arg` と `intro` の連続適用 |
| `rfl` | この部分は変更なしで完了 |

### 10.2 パターンマッチング

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]
```

### 10.3 ラムダ式内の書き換え

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv => lhs; intro x; rw [Nat.zero_add]
```

---

## 11. 公理と計算

### 11.1 Lean の公理体系

| 公理/定数 | 意味 |
|---|---|
| `propext` | 命題の外延性: `(a ↔ b) → a = b` |
| `funext` | 関数の外延性: `(∀ x, f x = g x) → f = g`（`Quot.sound` から導出） |
| `Quot.sound` | 商型の健全性: `r a b → Quot.mk r a = Quot.mk r b` |
| `Classical.choice` | 選択公理: `Nonempty α → α` |
| `Classical.em` | 排中律: `∀ p, p ∨ ¬p`（上記3つから導出） |

### 11.2 商型 (Quotient)

同値関係による商を構成する組み込み型:

```lean
-- Quot.mk r a : 元 a の同値類
-- Quot.lift f h : r を尊重する関数 f を商型上に持ち上げ
-- Quot.ind : 商型上の帰納法
```

### 11.3 noncomputable

`Classical.choice` に依存する定義は計算できないため `noncomputable` が必要:

```lean
open Classical
noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b => if ex : (∃ a, f a = b) then choose ex else default
```

### 11.4 Decidable と古典論理の関係

| アプローチ | `#eval` 実行可能 | 備考 |
|---|---|---|
| 構成的 `Decidable` インスタンス | ○ | `Nat.decLt` 等 |
| `open Classical` | × | 全 `Prop` が `Decidable` になるが `noncomputable` |

> **計算したい定義には構成的な `Decidable` インスタンスを使うべき。** `open Classical` は証明にのみ使い、実行コードでは避ける。

---

## 12. タクティク早見表

### 証明構築タクティク

| タクティク | 説明 | 例 |
|---|---|---|
| `exact t` | 項 `t` でゴールを閉じる | `exact hp` |
| `apply t` | `t` を適用、残りがサブゴール | `apply And.intro` |
| `intro x` | 仮定の導入 | `intro hp` |
| `constructor` | コンストラクタ適用 | `constructor` |
| `exists t` | 存在の証拠 | `exists 5` |
| `have h := ...` | 補助事実の導入 | `have h := h1.trans h2` |
| `show T` | ゴール型の明示 | `show p ∧ q` |
| `suffices h : T by ...` | 帰結を示せば十分 | `suffices h : p by ...` |

### 書き換え・簡約タクティク

| タクティク | 説明 | 例 |
|---|---|---|
| `rw [h₁, ← h₂]` | 等式で書き換え | `rw [Nat.add_comm]` |
| `simp [lemmas]` | 自動簡約 | `simp [Nat.add_assoc]` |
| `simp [*]` | 全仮定も利用 | `simp [*]` |
| `ring` | 環の等式 | `ring` |
| `omega` | 線形算術 | `omega` |
| `decide` | 決定可能命題 | `decide` |
| `norm_num` | 数値計算 | `norm_num` |

### 場合分け・帰納法タクティク

| タクティク | 説明 | 例 |
|---|---|---|
| `cases h with ...` | 帰納型の場合分け | `cases h with \| inl => ... \| inr => ...` |
| `induction x with ...` | 帰納法 | `induction n with \| zero => ... \| succ n ih => ...` |
| `rcases h with ⟨a, b⟩` | 再帰的場合分け | `rcases h with ⟨w, hw⟩` |
| `obtain ⟨a, b⟩ := h` | パターン分解 | `obtain ⟨w, hw⟩ := h` |
| `injection h` | コンストラクタの単射性 | `injection h` |

### 制御タクティク

| タクティク | 説明 |
|---|---|
| `assumption` | コンテキストから自動検索 |
| `contradiction` | 矛盾を検出 |
| `rfl` | 反射律 |
| `congr` | 合同ゴール生成 |
| `conv => ...` | 部分式の精密操作 |
| `<;> tac` | 全サブゴールに適用 |
| `first \| t₁ \| t₂` | 最初に成功するもの |

---

## 13. ベストプラクティス総括

### 証明戦略

1. **ゴールの型を理解する**: `show` で明示し、`#check` で関連する定理を探す
2. **単純な命題は項で証明**: ラムダ抽象と関数適用で構成。`⟨...⟩` を活用
3. **複雑な証明はタクティクで**: `by` でタクティクモードに入り、`apply`, `cases`, `induction` で分解
4. **自動化を活用**: `simp`, `omega`, `ring`, `decide` で済む場合は積極的に使う
5. **`calc` で段階的に**: 等式の連鎖は `calc` ブロックが可読性に優れる

### コーディング慣習

- `set_option autoImplicit false` を推奨（タイポ防止）
- 構成的な `Decidable` インスタンスを使い、`open Classical` は証明に限定
- `noncomputable` はやむを得ない場合のみ
- `sorry` はプロトタイピング専用。最終コードには残さない
- `termination_by` は省略せず明示することを推奨（複雑な場合）

### 型の設計

- パラメータ（固定）とインデックス（可変）の区別を意識して帰納型を定義
- `structure` は単一コンストラクタの場合に使用。`extends` で継承
- 型クラスで多相的な操作を定義し、インスタンスで具体化

### デバッグ

- `#check @f` で暗黙引数を確認
- `set_option pp.all true` で内部表現を確認
- `#print` で定義の展開を確認
- `trace_state` でタクティクの途中状態を確認

---

## 免責事項

本ドキュメントは非公式の解説・要約資料です。Lean プロジェクトおよびその著者（Jeremy Avigad, Leonardo de Moura, Soonho Kong, Sebastian Ullrich 各氏、および Lean Community の貢献者）とは一切関係がありません。内容の正確さについて一切保証しません。本ドキュメントを参照したことによって生じたいかなる損害についても、作成者は責任を負いません。

## ライセンス・著作権表記

本ドキュメントは以下の著作物を要約・再編集した派生物であり、Apache License 2.0 に基づいて頒布されます。

**原著作物:**

- 書名: *Theorem Proving in Lean 4*
- 著作権者: Copyright Jeremy Avigad, Leonardo de Moura, Soonho Kong, Sebastian Ullrich, and Lean Community contributors
- ライセンス: Apache License 2.0
- リポジトリ: <https://github.com/leanprover/theorem_proving_in_lean4>
- 公開 URL: <https://lean-lang.org/theorem_proving_in_lean4/>

本ドキュメントは原著作物を要約・再構成・注解・翻訳したものです。Apache License 2.0 の全文は <https://www.apache.org/licenses/LICENSE-2.0> を参照してください。
