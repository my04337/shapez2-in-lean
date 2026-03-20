# The Lean Language Reference — エージェント向けリファレンス索引

> **出典**: [The Lean Language Reference](https://lean-lang.org/doc/reference/latest/)
> Lean バージョン: 4.29.0-rc6

本ドキュメントは、Lean 4 の文法・機能を正確に調べる必要があるエージェントのための **リファレンスマニュアル索引** です。
各機能がマニュアルのどこに記載されているかを素早く特定するための手引きとして活用してください。

---

## 目次

1. [全章インデックス](#1-全章インデックス)
2. [章別サブセクション一覧](#2-章別サブセクション一覧)
3. [逆引きリファレンス — やりたいこと別索引](#3-逆引きリファレンス--やりたいこと別索引)
4. [タクティク一覧](#4-タクティク一覧)
5. [基本型一覧](#5-基本型一覧)
6. [理解が難しい概念の参照先](#6-理解が難しい概念の参照先)
7. [エージェント向け参照戦略](#7-エージェント向け参照戦略)

---

## 1. 全章インデックス

基本URL: `https://lean-lang.org/doc/reference/latest/`

| # | 章タイトル | URL |
|---|-----------|-----|
| 1 | Introduction | [Introduction/](https://lean-lang.org/doc/reference/latest/Introduction/) |
| 2 | Elaboration and Compilation | [Elaboration-and-Compilation/](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/) |
| 3 | Interacting with Lean | [Interacting-with-Lean/](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/) |
| 4 | The Type System | [The-Type-System/](https://lean-lang.org/doc/reference/latest/The-Type-System/) |
| 5 | Source Files and Modules | [Source-Files-and-Modules/](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/) |
| 6 | Namespaces and Sections | [Namespaces-and-Sections/](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/) |
| 7 | Definitions | [Definitions/](https://lean-lang.org/doc/reference/latest/Definitions/) |
| 8 | Axioms | [Axioms/](https://lean-lang.org/doc/reference/latest/Axioms/) |
| 9 | Attributes | [Attributes/](https://lean-lang.org/doc/reference/latest/Attributes/) |
| 10 | Type Classes | [Type-Classes/](https://lean-lang.org/doc/reference/latest/Type-Classes/) |
| 11 | Coercions | [Coercions/](https://lean-lang.org/doc/reference/latest/Coercions/) |
| 12 | Run-Time Code | [Run-Time-Code/](https://lean-lang.org/doc/reference/latest/Run-Time-Code/) |
| 13 | Terms | [Terms/](https://lean-lang.org/doc/reference/latest/Terms/) |
| 14 | Tactic Proofs | [Tactic-Proofs/](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/) |
| 15 | The Simplifier | [The-Simplifier/](https://lean-lang.org/doc/reference/latest/The-Simplifier/) |
| 16 | The `grind` tactic | [The--grind--tactic/](https://lean-lang.org/doc/reference/latest/The--grind--tactic/) |
| 17 | The `mvcgen` tactic | [The--mvcgen--tactic/](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/) |
| 18 | Functors, Monads and `do`-Notation | [Functors___-Monads-and--do--Notation/](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/) |
| 19 | Basic Propositions | [Basic-Propositions/](https://lean-lang.org/doc/reference/latest/Basic-Propositions/) |
| 20 | Basic Types | [Basic-Types/](https://lean-lang.org/doc/reference/latest/Basic-Types/) |
| 21 | IO | [IO/](https://lean-lang.org/doc/reference/latest/IO/) |
| 22 | Iterators | [Iterators/](https://lean-lang.org/doc/reference/latest/Iterators/) |
| 23 | Notations and Macros | [Notations-and-Macros/](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/) |
| 24 | Build Tools and Distribution | [Build-Tools-and-Distribution/](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/) |

**付録**:

| タイトル | URL |
|---------|-----|
| Validating a Lean Proof | [Validating-a-Lean-Proof/](https://lean-lang.org/doc/reference/latest/Validating-a-Lean-Proof/) |
| Error Explanations | [Error-Explanations/](https://lean-lang.org/doc/reference/latest/Error-Explanations/) |
| Release Notes | [Release-Notes/](https://lean-lang.org/doc/reference/latest/Release-Notes/) |
| Supported Platforms | [Supported-Platforms/](https://lean-lang.org/doc/reference/latest/Supported-Platforms/) |
| Index | [genindex/](https://lean-lang.org/doc/reference/latest/genindex/) |

---

## 2. 章別サブセクション一覧

### Ch3. Interacting with Lean

| # | セクション | 内容 |
|---|----------|------|
| 3.1 | [Evaluating Terms (`#eval`)](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-eval) | 式を評価して結果を表示 |
| 3.2 | [Reducing Terms (`#reduce`)](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-reduce) | 式をカーネルで簡約 |
| 3.3 | [Checking Types (`#check`)](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-check) | 式の型を表示 |
| 3.4 | [Synthesizing Instances (`#synth`)](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-synth) | インスタンス合成の確認 |
| 3.5 | [Querying the Context (`#print`)](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-print) | 定義・公理等の情報表示 |
| 3.6 | [Testing Output (`#guard_msgs`)](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-guard_msgs) | 出力メッセージのテスト |
| 3.7 | [Formatted Output](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#format-repr) | `Format` / `Repr` による整形出力 |

### Ch4. The Type System

| # | セクション | 内容 |
|---|----------|------|
| 4.1 | [Functions](https://lean-lang.org/doc/reference/latest/The-Type-System/Functions/) | 関数型・依存関数型 |
| 4.2 | [Propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/) | 命題と `Prop` |
| 4.3 | [Universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/) | 宇宙レベル (`Type u`, `Sort u`) |
| 4.4 | [Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/) | 帰納型・構造体・相互帰納型 |
| 4.5 | [Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/) | 商型 |

#### 4.4 Inductive Types の詳細

| サブセクション | 内容 |
|-------------|------|
| [4.4.1 Inductive Type Declarations](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive-declarations) | `inductive` 宣言の構文と規則 |
| [4.4.2 Structure Declarations](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structures) | `structure` 宣言・フィールド・継承 |
| [4.4.3 Logical Model](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive-types-logical-model) | 再帰子・整形性条件 |
| [4.4.4 Run-Time Representation](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#run-time-inductives) | 実行時表現・FFI |
| [4.4.5 Mutual Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#mutual-inductive-types) | 相互・ネスト帰納型 |

### Ch5. Source Files and Modules

| # | セクション | 内容 |
|---|----------|------|
| 5.1 | [Encoding and Representation](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-encoding) | UTF-8 エンコーディング |
| 5.2 | [Concrete Syntax](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-syntax) | 空白・コメント・キーワード・識別子 |
| 5.3 | [Structure](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-structure) | モジュールヘッダ・コマンド |
| 5.4 | [Modules and Visibility](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-scopes) | 可視性・メタフェーズ |
| 5.5 | [Elaborated Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-contents) | elaboration 後のモジュール |
| 5.6 | [Module System Errors and Patterns](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#The-Lean-Language-Reference--Source-Files-and-Modules--Module-System-Errors-and-Patterns) | エラーパターンと対処法 |
| 5.7 | [Packages, Libraries, and Targets](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#code-distribution) | パッケージ管理 |

### Ch6. Namespaces and Sections

| # | セクション | 内容 |
|---|----------|------|
| 6.1 | [Namespaces](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#namespaces) | 名前空間の定義と`export` |
| 6.2 | [Section Scopes](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#scopes) | `section`・`variable` コマンド |

### Ch7. Definitions

| # | セクション | 内容 |
|---|----------|------|
| 7.1 | [Modifiers](https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/) | `private` / `protected` / `noncomputable` 等 |
| 7.2 | [Headers and Signatures](https://lean-lang.org/doc/reference/latest/Definitions/Headers-and-Signatures/) | 定義のヘッダ構文 |
| 7.3 | [Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Definitions/) | `def` / `abbrev` |
| 7.4 | [Theorems](https://lean-lang.org/doc/reference/latest/Definitions/Theorems/) | `theorem` 宣言 |
| 7.5 | [Example Declarations](https://lean-lang.org/doc/reference/latest/Definitions/Example-Declarations/) | `example` 宣言 |
| 7.6 | [Recursive Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/) | 再帰定義（構造的/整礎/部分的） |

#### 7.6 Recursive Definitions の詳細

| サブセクション | 内容 |
|-------------|------|
| [7.6.1 Mutual Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#mutual-syntax) | `mutual ... end` 構文 |
| [7.6.2 Structural Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#structural-recursion) | 構造的再帰・推論 |
| [7.6.3 Well-Founded Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#well-founded-recursion) | 整礎再帰・`termination_by`・`decreasing_by` |
| [7.6.4 Partial Fixpoint Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#partial-fixpoint) | 部分不動点・末尾再帰 |
| [7.6.5 Partial and Unsafe Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#partial-unsafe) | `partial` / `unsafe` 修飾子 |
| [7.6.6 Controlling Reduction](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#reducibility) | `@[reducible]` / `@[irreducible]` |

### Ch8. Axioms

| # | セクション | 内容 |
|---|----------|------|
| 8.1 | [Axiom Declarations](https://lean-lang.org/doc/reference/latest/Axioms/#axiom-declarations) | `axiom` 宣言の構文 |
| 8.2 | [Consistency](https://lean-lang.org/doc/reference/latest/Axioms/#axiom-consistency) | 無矛盾性への影響 |
| 8.3 | [Reduction](https://lean-lang.org/doc/reference/latest/Axioms/#axiom-reduction) | 公理と簡約の関係 |
| 8.4 | [Standard Axioms](https://lean-lang.org/doc/reference/latest/Axioms/#standard-axioms) | `propext`, `Quot.sound`, `Classical.choice` 等 |
| 8.5 | [Displaying Axiom Dependencies (`#print axioms`)](https://lean-lang.org/doc/reference/latest/Axioms/#print-axioms) | 公理依存関係の表示 |

### Ch9. Attributes

| # | セクション | 内容 |
|---|----------|------|
| 9.1 | [Attributes as Modifiers](https://lean-lang.org/doc/reference/latest/Attributes/#The-Lean-Language-Reference--Attributes--Attributes-as-Modifiers) | `@[...]` 構文 |
| 9.2 | [The `attribute` Command](https://lean-lang.org/doc/reference/latest/Attributes/#The-Lean-Language-Reference--Attributes--The--attribute--Command) | 後付け属性設定 |
| 9.3 | [Scoped Attributes](https://lean-lang.org/doc/reference/latest/Attributes/#scoped-attributes) | スコープ付き属性 |

### Ch10. Type Classes

| # | セクション | 内容 |
|---|----------|------|
| 10.1 | [Class Declarations](https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/) | `class` 宣言 |
| 10.2 | [Instance Declarations](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/) | `instance` 宣言 |
| 10.3 | [Instance Synthesis](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/) | インスタンス合成メカニズム |
| 10.4 | [Deriving Instances](https://lean-lang.org/doc/reference/latest/Type-Classes/Deriving-Instances/) | `deriving` 自動導出 |
| 10.5 | [Basic Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/) | 基本クラス (`BEq`, `Hashable` 等) |

### Ch11. Coercions

| # | セクション | 内容 |
|---|----------|------|
| 11.1 | [Coercion Insertion](https://lean-lang.org/doc/reference/latest/Coercions/Coercion-Insertion/) | 型強制の挿入タイミング |
| 11.2 | [Coercing Between Types](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-Between-Types/) | 型間の強制 (`Coe`) |
| 11.3 | [Coercing to Sorts](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-to-Sorts/) | `CoeSort`（型への強制） |
| 11.4 | [Coercing to Function Types](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-to-Function-Types/) | `CoeFun`（関数型への強制） |
| 11.5 | [Implementation Details](https://lean-lang.org/doc/reference/latest/Coercions/Implementation-Details/) | 内部実装 |

### Ch12. Run-Time Code

| # | セクション | 内容 |
|---|----------|------|
| 12.1 | [Boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/) | ボクシング・アンボクシング |
| 12.2 | [Reference Counting](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/) | 参照カウントGC |
| 12.3 | [Multi-Threaded Execution](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Multi-Threaded-Execution/) | マルチスレッド実行 |
| 12.4 | [Foreign Function Interface](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/) | FFI (C言語連携) |

### Ch13. Terms

| # | セクション | 内容 |
|---|----------|------|
| 13.1 | [Identifiers](https://lean-lang.org/doc/reference/latest/Terms/Identifiers/) | 識別子の解決 |
| 13.2 | [Function Types](https://lean-lang.org/doc/reference/latest/Terms/Function-Types/) | `→` / `∀` 型構文 |
| 13.3 | [Functions](https://lean-lang.org/doc/reference/latest/Terms/Functions/) | `fun` / `λ` 式 |
| 13.4 | [Function Application](https://lean-lang.org/doc/reference/latest/Terms/Function-Application/) | 関数適用・名前付き引数 |
| 13.5 | [Numeric Literals](https://lean-lang.org/doc/reference/latest/Terms/Numeric-Literals/) | 数値リテラル |
| 13.6 | [Structures and Constructors](https://lean-lang.org/doc/reference/latest/Terms/Structures-and-Constructors/) | `{ ... }` / `⟨...⟩` 式 |
| 13.7 | [Conditionals](https://lean-lang.org/doc/reference/latest/Terms/Conditionals/) | `if ... then ... else` |
| 13.8 | [Pattern Matching](https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/) | `match` 式 |
| 13.9 | [Holes](https://lean-lang.org/doc/reference/latest/Terms/Holes/) | `_` / `?x` プレースホルダ |
| 13.10 | [Type Ascription](https://lean-lang.org/doc/reference/latest/Terms/Type-Ascription/) | `(expr : Type)` 型注釈 |
| 13.11 | [Quotation and Antiquotation](https://lean-lang.org/doc/reference/latest/Terms/Quotation-and-Antiquotation/) | `` `(syntax) `` / `$x` マクロ用 |
| 13.12 | [`do`-Notation](https://lean-lang.org/doc/reference/latest/Terms/Do-Notation/) | `do` ブロック構文 |
| 13.13 | [Proofs](https://lean-lang.org/doc/reference/latest/Terms/Proofs/) | 項証明モード |

### Ch14. Tactic Proofs

| # | セクション | 内容 |
|---|----------|------|
| 14.1 | [Running Tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Running-Tactics/) | `by` ブロック |
| 14.2 | [Reading Proof States](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Reading-Proof-States/) | 証明状態の読み方 |
| 14.3 | [The Tactic Language](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/The-Tactic-Language/) | タクティク言語の構文 |
| 14.4 | [Options](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Options/) | タクティクオプション |
| 14.5 | [Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) | **全タクティクリファレンス** |
| 14.6 | [Targeted Rewriting with `conv`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Targeted-Rewriting-with--conv/) | `conv` モード |
| 14.7 | [Naming Bound Variables](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Naming-Bound-Variables/) | 束縛変数の命名 |
| 14.8 | [Custom Tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Custom-Tactics/) | カスタムタクティク作成 |

### Ch15. The Simplifier

| # | セクション | 内容 |
|---|----------|------|
| 15.1 | [Invoking the Simplifier](https://lean-lang.org/doc/reference/latest/The-Simplifier/Invoking-the-Simplifier/) | `simp` の呼び出し方 |
| 15.2 | [Rewrite Rules](https://lean-lang.org/doc/reference/latest/The-Simplifier/Rewrite-Rules/) | 書き換え規則の定義 |
| 15.3 | [Simp Sets](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/) | simp セットの管理 |
| 15.4 | [Simp Normal Forms](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-Normal-Forms/) | 正規形 |
| 15.5 | [Terminal vs Non-Terminal Positions](https://lean-lang.org/doc/reference/latest/The-Simplifier/Terminal-vs-Non-Terminal-Positions/) | 末尾/非末尾位置の違い |
| 15.6 | [Configuring Simplification](https://lean-lang.org/doc/reference/latest/The-Simplifier/Configuring-Simplification/) | 設定オプション |
| 15.7 | [Simplification vs Rewriting](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simplification-vs-Rewriting/) | `simp` vs `rw` の使い分け |

### Ch16. The `grind` tactic

| # | セクション | 内容 |
|---|----------|------|
| 16.1 | [Error Messages](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Error-Messages/) | エラーメッセージ |
| 16.2 | [Minimizing `grind` calls](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Minimizing--grind--calls/) | grind 呼び出しの最小化 |
| 16.3 | [Congruence Closure](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Congruence-Closure/) | 合同閉包 |
| 16.4 | [Constraint Propagation](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Constraint-Propagation/) | 制約伝搬 |
| 16.5 | [Case Analysis](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Case-Analysis/) | ケース分析 |
| 16.6 | [E-matching](https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/) | E マッチング |
| 16.7 | [Linear Integer Arithmetic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Integer-Arithmetic/) | 線形整数算術 |
| 16.8 | [Algebraic Solver](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Algebraic-Solver-_LPAR_Commutative-Rings___-Fields_RPAR_/) | 可換環・体のソルバー |
| 16.9 | [Linear Arithmetic Solver](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Arithmetic-Solver/) | 線形算術ソルバー |
| 16.10 | [Annotating Libraries for `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Annotating-Libraries-for--grind/) | ライブラリのアノテーション |
| 16.11 | [Reducibility](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Reducibility/) | 簡約可能性設定 |
| 16.12 | [Bigger Examples](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Bigger-Examples/) | 大きな証明例 |

### Ch17. The `mvcgen` tactic

| # | セクション | 内容 |
|---|----------|------|
| 17.1 | [Overview](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Overview/) | 概要 |
| 17.2 | [Predicate Transformers](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Predicate-Transformers/) | 述語変換子 |
| 17.3 | [Verification Conditions](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Verification-Conditions/) | 検証条件 |
| 17.4 | [Enabling `mvcgen` For Monads](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Enabling--mvcgen--For-Monads/) | モナドへの有効化 |
| 17.5 | [Proof Mode](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Proof-Mode/) | 証明モード |

### Ch18. Functors, Monads and `do`-Notation

| # | セクション | 内容 |
|---|----------|------|
| 18.1 | [Laws](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Laws/) | ファンクタ・モナド則 |
| 18.2 | [Lifting Monads](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Lifting-Monads/) | `MonadLift` / `MonadControl` |
| 18.3 | [Syntax](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/) | `do` 構文の詳細 |
| 18.4 | [API Reference](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/API-Reference/) | `Functor` / `Applicative` / `Monad` API |
| 18.5 | [Varieties of Monads](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Varieties-of-Monads/) | `StateM`, `ReaderM`, `ExceptT` 等 |

### Ch19. Basic Propositions

| # | セクション | 内容 |
|---|----------|------|
| 19.1 | [Truth](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Truth/) | `True` / `False` |
| 19.2 | [Logical Connectives](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Logical-Connectives/) | `∧` / `∨` / `¬` / `→` / `↔` |
| 19.3 | [Quantifiers](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Quantifiers/) | `∀` / `∃` |
| 19.4 | [Propositional Equality](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/) | `=` / `Eq` |

### Ch20. Basic Types

| # | セクション | 内容 |
|---|----------|------|
| 20.1 | [Natural Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/) | `Nat` |
| 20.2 | [Integers](https://lean-lang.org/doc/reference/latest/Basic-Types/Integers/) | `Int` |
| 20.3 | [Finite Natural Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Finite-Natural-Numbers/) | `Fin n` |
| 20.4 | [Fixed-Precision Integers](https://lean-lang.org/doc/reference/latest/Basic-Types/Fixed-Precision-Integers/) | `UInt8`, `UInt32`, `UInt64` 等 |
| 20.5 | [Bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/) | `BitVec n` |
| 20.6 | [Floating-Point Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/) | `Float` |
| 20.7 | [Characters](https://lean-lang.org/doc/reference/latest/Basic-Types/Characters/) | `Char` |
| 20.8 | [Strings](https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/) | `String` |
| 20.9 | [The Unit Type](https://lean-lang.org/doc/reference/latest/Basic-Types/The-Unit-Type/) | `Unit` / `()` |
| 20.10 | [The Empty Type](https://lean-lang.org/doc/reference/latest/Basic-Types/The-Empty-Type/) | `Empty` |
| 20.11 | [Booleans](https://lean-lang.org/doc/reference/latest/Basic-Types/Booleans/) | `Bool` |
| 20.12 | [Optional Values](https://lean-lang.org/doc/reference/latest/Basic-Types/Optional-Values/) | `Option α` |
| 20.13 | [Tuples](https://lean-lang.org/doc/reference/latest/Basic-Types/Tuples/) | `Prod` / `(a, b)` |
| 20.14 | [Sum Types](https://lean-lang.org/doc/reference/latest/Basic-Types/Sum-Types/) | `Sum α β` |
| 20.15 | [Linked Lists](https://lean-lang.org/doc/reference/latest/Basic-Types/Linked-Lists/) | `List α` |
| 20.16 | [Arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/) | `Array α` / `#[...]` |
| 20.17 | [Byte Arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Byte-Arrays/) | `ByteArray` |
| 20.18 | [Ranges](https://lean-lang.org/doc/reference/latest/Basic-Types/Ranges/) | `Range` / `[0:n]` |
| 20.19 | [Maps and Sets](https://lean-lang.org/doc/reference/latest/Basic-Types/Maps-and-Sets/) | `HashMap`, `RBMap` 等 |
| 20.20 | [Subtypes](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/) | `Subtype` / `{ x : α // p x }` |
| 20.21 | [Lazy Computations](https://lean-lang.org/doc/reference/latest/Basic-Types/Lazy-Computations/) | `Thunk` / 遅延評価 |

### Ch21. IO

| # | セクション | 内容 |
|---|----------|------|
| 21.1 | [Logical Model](https://lean-lang.org/doc/reference/latest/IO/Logical-Model/) | IO モナドの論理モデル |
| 21.2 | [Control Structures](https://lean-lang.org/doc/reference/latest/IO/Control-Structures/) | 制御構造 |
| 21.3 | [Console Output](https://lean-lang.org/doc/reference/latest/IO/Console-Output/) | `IO.println` 等 |
| 21.4 | [Mutable References](https://lean-lang.org/doc/reference/latest/IO/Mutable-References/) | `IO.Ref` |
| 21.5 | [Files, File Handles, and Streams](https://lean-lang.org/doc/reference/latest/IO/Files___-File-Handles___-and-Streams/) | ファイル操作 |
| 21.6 | [System and Platform Information](https://lean-lang.org/doc/reference/latest/IO/System-and-Platform-Information/) | システム情報取得 |
| 21.7 | [Environment Variables](https://lean-lang.org/doc/reference/latest/IO/Environment-Variables/) | 環境変数 |
| 21.8 | [Timing](https://lean-lang.org/doc/reference/latest/IO/Timing/) | 計時 API |
| 21.9 | [Processes](https://lean-lang.org/doc/reference/latest/IO/Processes/) | 外部プロセス実行 |
| 21.10 | [Random Numbers](https://lean-lang.org/doc/reference/latest/IO/Random-Numbers/) | 乱数生成 |
| 21.11 | [Tasks and Threads](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/) | 非同期タスク・スレッド |

### Ch22. Iterators

| # | セクション | 内容 |
|---|----------|------|
| 22.1 | [Run-Time Considerations](https://lean-lang.org/doc/reference/latest/Iterators/Run-Time-Considerations/) | パフォーマンス |
| 22.2 | [Iterator Definitions](https://lean-lang.org/doc/reference/latest/Iterators/Iterator-Definitions/) | イテレータの定義方法 |
| 22.3 | [Consuming Iterators](https://lean-lang.org/doc/reference/latest/Iterators/Consuming-Iterators/) | イテレータの消費 |
| 22.4 | [Iterator Combinators](https://lean-lang.org/doc/reference/latest/Iterators/Iterator-Combinators/) | コンビネータ (`map`, `filter` 等) |
| 22.5 | [Reasoning About Iterators](https://lean-lang.org/doc/reference/latest/Iterators/Reasoning-About-Iterators/) | イテレータの推論 |

### Ch23. Notations and Macros

| # | セクション | 内容 |
|---|----------|------|
| 23.1 | [Custom Operators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Custom-Operators/) | カスタム演算子の定義 |
| 23.2 | [Precedence](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Precedence/) | 優先度規則 |
| 23.3 | [Notations](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Notations/) | `notation` コマンド |
| 23.4 | [Defining New Syntax](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Defining-New-Syntax/) | `syntax` / `syntax_cat` |
| 23.5 | [Macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/) | `macro` / `macro_rules` |
| 23.6 | [Elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/) | `elab` / エラボレータ |
| 23.7 | [Extending Lean's Output](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Extending-Lean___s-Output/) | 出力のカスタマイズ |

### Ch24. Build Tools and Distribution

| # | セクション | 内容 |
|---|----------|------|
| 24.1 | [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) | Lake ビルドシステム |
| 24.2 | [Managing Toolchains with Elan](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/) | Elan ツールチェーン管理 |

---

## 3. 逆引きリファレンス — やりたいこと別索引

### 型定義・データ構造

| やりたいこと | 参照先 |
|------------|--------|
| 新しい型を定義したい | [Ch4.4 Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/) |
| 構造体を定義したい | [Ch4.4.2 Structures](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structures) |
| 構造体の継承を使いたい | [Ch4.4.2.4 Structure Inheritance](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structure-inheritance) |
| 列挙型を定義したい | [Ch4.4.1 Inductive Type Declarations](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive-declarations) |
| 相互帰納型を使いたい | [Ch4.4.5 Mutual Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#mutual-inductive-types) |
| ネスト帰納型を使いたい | [Ch4.4.5.4 Nested Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#nested-inductive-types) |
| 商型を使いたい | [Ch4.5 Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/) |
| 部分型（条件付き型）を使いたい | [Ch20.20 Subtypes](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/) |

### 関数定義・再帰

| やりたいこと | 参照先 |
|------------|--------|
| 関数を定義したい (`def`) | [Ch7.3 Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Definitions/) |
| 再帰関数を定義したい | [Ch7.6 Recursive Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/) |
| 停止性を証明したい (`termination_by`) | [Ch7.6.3 Well-Founded Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#well-founded-recursion) |
| `partial` を使いたい（停止性を諦める） | [Ch7.6.5 Partial and Unsafe](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#partial-unsafe) |
| `unsafe` を使いたい | [Ch7.6.5.2 Unsafe Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#unsafe) |
| `abbrev` と `def` の違いを知りたい | [Ch7.3 Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Definitions/) + [Ch7.6.6 Controlling Reduction](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#reducibility) |
| 相互再帰関数を書きたい | [Ch7.6.1 Mutual Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#mutual-syntax) |
| `private` / `protected` 修飾子を使いたい | [Ch7.1 Modifiers](https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/) |

### 型クラス・多態性

| やりたいこと | 参照先 |
|------------|--------|
| 型クラスを定義したい | [Ch10.1 Class Declarations](https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/) |
| インスタンスを宣言したい | [Ch10.2 Instance Declarations](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/) |
| インスタンス合成の仕組みを知りたい | [Ch10.3 Instance Synthesis](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/) |
| `deriving` を使いたい | [Ch10.4 Deriving Instances](https://lean-lang.org/doc/reference/latest/Type-Classes/Deriving-Instances/) |
| 基本型クラス (`BEq`, `Repr` 等) | [Ch10.5 Basic Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/) |
| 型強制を定義したい (`Coe`) | [Ch11.2 Coercing Between Types](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-Between-Types/) |
| `CoeSort` / `CoeFun` を使いたい | [Ch11.3](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-to-Sorts/) / [Ch11.4](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-to-Function-Types/) |

### 証明・タクティク

| やりたいこと | 参照先 |
|------------|--------|
| タクティクの一覧を見たい | [Ch14.5 Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) |
| `by` ブロックの書き方 | [Ch14.1 Running Tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Running-Tactics/) |
| 証明状態の読み方 | [Ch14.2 Reading Proof States](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Reading-Proof-States/) |
| `simp` の使い方・設定 | [Ch15 The Simplifier](https://lean-lang.org/doc/reference/latest/The-Simplifier/) |
| `simp` と `rw` の違い | [Ch15.7 Simplification vs Rewriting](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simplification-vs-Rewriting/) |
| `@[simp]` 属性の管理 | [Ch15.2 Rewrite Rules](https://lean-lang.org/doc/reference/latest/The-Simplifier/Rewrite-Rules/) + [Ch15.3 Simp sets](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/) |
| `grind` タクティクを使いたい | [Ch16 The `grind` tactic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/) |
| `conv` モードで部分書き換えしたい | [Ch14.6 Targeted Rewriting with `conv`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Targeted-Rewriting-with--conv/) |
| カスタムタクティクを作りたい | [Ch14.8 Custom Tactics](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Custom-Tactics/) |
| `mvcgen` で検証条件を生成したい | [Ch17 The `mvcgen` tactic](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/) |

### 命題・論理

| やりたいこと | 参照先 |
|------------|--------|
| 論理結合子 (`∧`, `∨`, `¬`, `↔`) | [Ch19.2 Logical Connectives](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Logical-Connectives/) |
| 全称・存在量化子 (`∀`, `∃`) | [Ch19.3 Quantifiers](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Quantifiers/) |
| 命題的等値 (`=`) | [Ch19.4 Propositional Equality](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/) |
| `Prop` と `Type` の違い | [Ch4.2 Propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/) |
| 宇宙レベル (`Type u`, `Sort u`) | [Ch4.3 Universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/) |
| 標準公理 (`propext`, `Classical.choice` 等) | [Ch8.4 Standard Axioms](https://lean-lang.org/doc/reference/latest/Axioms/#standard-axioms) |

### 式・構文

| やりたいこと | 参照先 |
|------------|--------|
| `match` 式でパターンマッチしたい | [Ch13.8 Pattern Matching](https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/) |
| `if ... then ... else` の構文 | [Ch13.7 Conditionals](https://lean-lang.org/doc/reference/latest/Terms/Conditionals/) |
| 名前付き引数・デフォルト引数 | [Ch13.4 Function Application](https://lean-lang.org/doc/reference/latest/Terms/Function-Application/) |
| `_` ホール・自動推論 | [Ch13.9 Holes](https://lean-lang.org/doc/reference/latest/Terms/Holes/) |
| 構造体リテラル `{ field := val }` | [Ch13.6 Structures and Constructors](https://lean-lang.org/doc/reference/latest/Terms/Structures-and-Constructors/) |
| 匿名コンストラクタ `⟨a, b⟩` | [Ch4.4.1.3 Anonymous Constructor Syntax](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#anonymous-constructor-syntax) |
| `do` 記法の完全な構文 | [Ch13.12 `do`-Notation](https://lean-lang.org/doc/reference/latest/Terms/Do-Notation/) + [Ch18.3 Syntax](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/) |
| 数値リテラルの仕組み | [Ch13.5 Numeric Literals](https://lean-lang.org/doc/reference/latest/Terms/Numeric-Literals/) |
| Quotation / Antiquotation（マクロ用） | [Ch13.11 Quotation](https://lean-lang.org/doc/reference/latest/Terms/Quotation-and-Antiquotation/) |

### モナド・副作用

| やりたいこと | 参照先 |
|------------|--------|
| `Functor` / `Applicative` / `Monad` の API | [Ch18.4 API Reference](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/API-Reference/) |
| モナド則を知りたい | [Ch18.1 Laws](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Laws/) |
| `StateM` / `ReaderM` / `ExceptT` 等 | [Ch18.5 Varieties of Monads](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Varieties-of-Monads/) |
| `MonadLift` / モナド変換子 | [Ch18.2 Lifting Monads](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Lifting-Monads/) |
| IO 操作を行いたい | [Ch21 IO](https://lean-lang.org/doc/reference/latest/IO/) |
| ファイル読み書き | [Ch21.5 Files, File Handles, and Streams](https://lean-lang.org/doc/reference/latest/IO/Files___-File-Handles___-and-Streams/) |
| 外部プロセスを実行したい | [Ch21.9 Processes](https://lean-lang.org/doc/reference/latest/IO/Processes/) |
| 非同期・並行処理 | [Ch21.11 Tasks and Threads](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/) |

### DSL・拡張・メタプログラミング

| やりたいこと | 参照先 |
|------------|--------|
| カスタム演算子を定義したい | [Ch23.1 Custom Operators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Custom-Operators/) |
| 演算子の優先度を設定したい | [Ch23.2 Precedence](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Precedence/) |
| `notation` コマンドを使いたい | [Ch23.3 Notations](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Notations/) |
| 新しい構文カテゴリを作りたい | [Ch23.4 Defining New Syntax](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Defining-New-Syntax/) |
| マクロを書きたい | [Ch23.5 Macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/) |
| エラボレータを書きたい | [Ch23.6 Elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/) |
| 属性を付与・管理したい | [Ch9 Attributes](https://lean-lang.org/doc/reference/latest/Attributes/) |

### プロジェクト管理・ビルド

| やりたいこと | 参照先 |
|------------|--------|
| Lake の使い方 | [Ch24.1 Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) |
| Elan でツールチェーンを管理したい | [Ch24.2 Elan](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/) |
| モジュールの `import` 構文 | [Ch5.3.1 Headers](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-headers) |
| 名前空間の `open` / `export` | [Ch6.1 Namespaces](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#namespaces) |
| `section` / `variable` | [Ch6.2 Section Scopes](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#scopes) |
| パッケージ・ライブラリ管理 | [Ch5.7 Packages, Libraries, and Targets](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#code-distribution) |

### デバッグ・調査

| やりたいこと | 参照先 |
|------------|--------|
| `#eval` で式を評価したい | [Ch3.1 Evaluating Terms](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-eval) |
| `#check` で型を確認したい | [Ch3.3 Checking Types](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-check) |
| `#print` で定義を見たい | [Ch3.5 Querying the Context](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-print) |
| `#print axioms` で公理依存を見たい | [Ch8.5 Displaying Axiom Dependencies](https://lean-lang.org/doc/reference/latest/Axioms/#print-axioms) |
| `sorry` で仮に証明をスキップしたい | [Ch14.5 Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) (Debugging Utilities) |
| `exact?` / `apply?` で補題を検索 | [Ch14.5 Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) (Library Search) |
| エラーメッセージの意味を知りたい | [Error Explanations](https://lean-lang.org/doc/reference/latest/Error-Explanations/) |
| `Repr` / `ToString` の実装 | [Ch3.7 Formatted Output](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#format-repr) |

### 実行時・FFI

| やりたいこと | 参照先 |
|------------|--------|
| C 言語と連携したい (FFI) | [Ch12.4 Foreign Function Interface](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/) |
| 実行時のメモリ管理を理解したい | [Ch12.2 Reference Counting](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/) |
| ボクシングの仕組み | [Ch12.1 Boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/) |
| マルチスレッド時の注意点 | [Ch12.3 Multi-Threaded Execution](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Multi-Threaded-Execution/) |

---

## 4. タクティク一覧

[Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) に全タクティクの詳細があります。以下はカテゴリ別の概要です。

### 古典論理

| タクティク | 用途 |
|-----------|------|
| `classical` | 古典的推論を利用可能にする |

### 仮定の利用

| タクティク | 用途 |
|-----------|------|
| `assumption` | 仮定からゴールを閉じる |
| `apply_assumption` | 仮定を適用する |

### 量化子

| タクティク | 用途 |
|-----------|------|
| `intro` / `intros` | 仮定を導入 |
| `rintro` | パターン付き導入 |
| `exists` | 存在量化の証人を与える |

### 関係・等式

| タクティク | 用途 |
|-----------|------|
| `rfl` | 反射律でゴールを閉じる |
| `symm` | 等式を左右入れ替え |
| `calc` | 計算証明チェーン |
| `subst` | 等式で置換 |
| `congr` | 合同律の適用 |
| `ac_rfl` | 結合・可換律で閉じる |

### 補題の適用

| タクティク | 用途 |
|-----------|------|
| `exact` | 証明項を直接与える |
| `apply` | 補題を後ろ向きに適用 |
| `refine` | ホール付きで証明項を与える |
| `apply_rules` | ルールセットで自動適用 |

### 矛盾

| タクティク | 用途 |
|-----------|------|
| `exfalso` | ゴールを `False` に変更 |
| `contradiction` | 仮定から矛盾を導出 |

### ゴール管理

| タクティク | 用途 |
|-----------|------|
| `suffices` | 中間目標を設定 |
| `change` | ゴールを定義上等しい式に変更 |
| `generalize` | 項を一般化 |
| `specialize` | 仮定を特殊化 |
| `obtain` | 仮定をデストラクチャ |
| `show` | ゴールを明示 |

### 簡約・書き換え

| タクティク | 用途 |
|-----------|------|
| `simp` | 自動簡約（シンプリファイア） |
| `rw` / `rewrite` | 指定した等式で書き換え |
| `erw` | 定義展開+書き換え |
| `rwa` | 書き換え後に `assumption` |
| `unfold` | 定義を展開 |
| `delta` | デルタ展開 |
| `norm_cast` | キャスト正規化 |

### 帰納型

| タクティク | 用途 |
|-----------|------|
| `constructor` | コンストラクタを適用 |
| `injection` | コンストラクタの単射性 |
| `left` / `right` | `Or` のどちらかを選択 |
| `cases` / `rcases` | ケース分析 |
| `induction` | 帰納法 |
| `nofun` / `nomatch` | 空パターンによる証明 |

### ライブラリ検索

| タクティク | 用途 |
|-----------|------|
| `exact?` | ゴールを閉じる補題を検索 |
| `apply?` | 適用可能な補題を検索 |
| `rw?` | 適用可能な書き換え規則を検索 |

### 場合分け・決定手続き

| タクティク | 用途 |
|-----------|------|
| `split` | `if` / `match` の場合分け |
| `by_cases` | 排中律による場合分け |
| `omega` | 自然数・整数の線形算術 |
| `decide` | 決定可能命題の自動判定 |
| `native_decide` | ネイティブコードで `decide` |
| `bv_decide` | ビットベクタの決定手続き |

### 自動化

| タクティク | 用途 |
|-----------|------|
| `grind` | SMT 風の自動証明 |
| `mvcgen` | 検証条件生成 |
| `trivial` | 自明なゴールを閉じる |

### デバッグ

| タクティク | 用途 |
|-----------|------|
| `sorry` / `admit` | 証明を仮にスキップ |
| `dbg_trace` | デバッグ出力 |
| `trace_state` | 証明状態のトレース |

### その他

| タクティク | 用途 |
|-----------|------|
| `ext` | 外延性 |
| `infer_instance` | インスタンスの推論 |
| `run_tac` | メタプログラムを実行 |
| `decreasing_with` | 停止性証明タクティク |

### `mvcgen` 証明モード専用タクティク

| タクティク | 用途 |
|-----------|------|
| `mstart` / `mstop` / `mleave` | モード開始・終了 |
| `mintro` / `mexact` / `massumption` | 導入・適用 |
| `mcases` / `mconstructor` | ケース分析・構築 |
| `mleft` / `mright` / `mexists` | 選択・存在 |
| `mpure_intro` / `mpure` | 純粋計算 |
| `mframe` | フレーム規則 |
| `mexfalso` | 矛盾 |

---

## 5. 基本型一覧

[Ch20 Basic Types](https://lean-lang.org/doc/reference/latest/Basic-Types/) の全型一覧です。

### 数値型

| 型 | 説明 | 参照先 |
|---|------|--------|
| `Nat` | 自然数（任意精度） | [Natural Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/) |
| `Int` | 整数（任意精度） | [Integers](https://lean-lang.org/doc/reference/latest/Basic-Types/Integers/) |
| `Fin n` | 0 以上 n 未満の自然数 | [Finite Natural Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Finite-Natural-Numbers/) |
| `UInt8` / `UInt16` / `UInt32` / `UInt64` / `USize` | 固定精度整数 | [Fixed-Precision Integers](https://lean-lang.org/doc/reference/latest/Basic-Types/Fixed-Precision-Integers/) |
| `BitVec n` | n ビットベクタ | [Bitvectors](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/) |
| `Float` | 浮動小数点数 | [Floating-Point Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/) |

### テキスト型

| 型 | 説明 | 参照先 |
|---|------|--------|
| `Char` | Unicode 文字 | [Characters](https://lean-lang.org/doc/reference/latest/Basic-Types/Characters/) |
| `String` | 文字列 | [Strings](https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/) |

### 基本型

| 型 | 説明 | 参照先 |
|---|------|--------|
| `Unit` / `()` | 単位型 | [The Unit Type](https://lean-lang.org/doc/reference/latest/Basic-Types/The-Unit-Type/) |
| `Empty` | 空型（値なし） | [The Empty Type](https://lean-lang.org/doc/reference/latest/Basic-Types/The-Empty-Type/) |
| `Bool` | 真偽値 | [Booleans](https://lean-lang.org/doc/reference/latest/Basic-Types/Booleans/) |

### コンテナ型

| 型 | 説明 | 参照先 |
|---|------|--------|
| `Option α` | 省略可能な値 | [Optional Values](https://lean-lang.org/doc/reference/latest/Basic-Types/Optional-Values/) |
| `Prod α β` / `(a, b)` | タプル（直積） | [Tuples](https://lean-lang.org/doc/reference/latest/Basic-Types/Tuples/) |
| `Sum α β` | 直和型 | [Sum Types](https://lean-lang.org/doc/reference/latest/Basic-Types/Sum-Types/) |
| `List α` | 連結リスト | [Linked Lists](https://lean-lang.org/doc/reference/latest/Basic-Types/Linked-Lists/) |
| `Array α` | 動的配列 | [Arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/) |
| `ByteArray` | バイト配列 | [Byte Arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Byte-Arrays/) |
| `Range` / `[0:n]` | 範囲 | [Ranges](https://lean-lang.org/doc/reference/latest/Basic-Types/Ranges/) |
| `HashMap` / `RBMap` 等 | マップ・セット | [Maps and Sets](https://lean-lang.org/doc/reference/latest/Basic-Types/Maps-and-Sets/) |

### 特殊型

| 型 | 説明 | 参照先 |
|---|------|--------|
| `Subtype` / `{ x : α // p x }` | 条件付き部分型 | [Subtypes](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/) |
| `Thunk α` | 遅延計算 | [Lazy Computations](https://lean-lang.org/doc/reference/latest/Basic-Types/Lazy-Computations/) |

---

## 6. 理解が難しい概念の参照先

以下は Lean 4 を使う際に混乱しやすい概念と、正確な情報が得られるリファレンスページの対応です。

### 宇宙レベル (`Type u`, `Sort u`, `Prop`)

- **参照先**: [Ch4.3 Universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)
- **ポイント**: `Prop = Sort 0`, `Type u = Sort (u+1)`。宇宙多相を使う場面とオートバウンドの仕組みを理解する。

### Subsingleton Elimination

- **参照先**: [Ch4.4.3.1.1.1 Subsingleton Elimination](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#subsingleton-elimination)
- **ポイント**: `Prop` 型の帰納型から `Type` レベルの値を取り出す際の制限。なぜ `Or` を `match` できないかに関連。

### Strict Positivity

- **参照先**: [Ch4.4.3.2 Well-Formedness Requirements](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#well-formed-inductives)
- **ポイント**: 帰納型のコンストラクタ引数での再帰型の出現位置の制限。

### 構造的再帰 vs 整礎再帰

- **参照先**: [Ch7.6.2 Structural Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#structural-recursion) / [Ch7.6.3 Well-Founded Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#well-founded-recursion)
- **ポイント**: Lean はまず構造的再帰を試み、失敗すると整礎再帰にフォールバックする。`termination_by` と `decreasing_by` で停止性証明を制御。

### `noncomputable` と計算不可能性

- **参照先**: [Ch7.1 Modifiers](https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/)
- **ポイント**: `Classical.choice` 等の公理に依存する定義は計算不可能になる。`#eval` できない場合にこれを確認。

### インスタンス合成の動作

- **参照先**: [Ch10.3 Instance Synthesis](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/)
- **ポイント**: バックトラッキング検索。インスタンスの優先度、`outParam` の扱い、合成失敗時のデバッグ。

### 型強制 (`Coe`, `CoeSort`, `CoeFun`)

- **参照先**: [Ch11 Coercions](https://lean-lang.org/doc/reference/latest/Coercions/)
- **ポイント**: 3 種類の強制がある — 型間、ソートへ、関数型への強制。意図しない強制が挿入される場合のデバッグに有用。

### `do` 記法の糖衣構文展開

- **参照先**: [Ch18.3 Syntax](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/) + [Ch13.12 `do`-Notation](https://lean-lang.org/doc/reference/latest/Terms/Do-Notation/)
- **ポイント**: `let mut`, `for ... in`, `return`, `if let` 等の展開先を理解する。早期リターンは `ExceptT` に変換される。

### 簡約可能性 (`@[reducible]`, `@[irreducible]`)

- **参照先**: [Ch7.6.6 Controlling Reduction](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#reducibility)
- **ポイント**: `abbrev` は暗黙に `@[reducible]`。`simp` / `unfold` の挙動に影響。

### `Prop` vs `Bool` (決定可能性)

- **参照先**: [Ch4.2 Propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/) + [Ch20.11 Booleans](https://lean-lang.org/doc/reference/latest/Basic-Types/Booleans/)
- **ポイント**: `Prop` は証明、`Bool` は計算。`Decidable` インスタンスにより `if` で `Prop` を使える。

### 商型 (`Quot`, `Quotient`)

- **参照先**: [Ch4.5 Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/)
- **ポイント**: `Quot.sound` 公理に基づく。同値関係による型の商を構成。

### Elaboration とメタフェーズ

- **参照先**: [Ch2 Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/) + [Ch5.4.1 The Meta Phase](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#meta-phase)
- **ポイント**: Lean のコード処理パイプラインの理解。`initialize` ブロック等のメタ操作。

---

## 7. エージェント向け参照戦略

### いつ何を参照すべきか

| 状況 | 最初に参照すべき箇所 |
|------|-------------------|
| 構文エラーが出た | [Ch13 Terms](https://lean-lang.org/doc/reference/latest/Terms/) — 該当する式の構文を確認 |
| 型エラーが出た | [Ch4 The Type System](https://lean-lang.org/doc/reference/latest/The-Type-System/) — 型規則を確認 |
| タクティクが失敗した | [Ch14.5 Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) — タクティクの前提条件を確認 |
| `simp` が期待通り動かない | [Ch15 The Simplifier](https://lean-lang.org/doc/reference/latest/The-Simplifier/) — simp セットと設定を確認 |
| 停止性証明に失敗した | [Ch7.6.3 Well-Founded Recursion](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#well-founded-recursion) — `termination_by` / `decreasing_by` |
| import / namespace の問題 | [Ch5 Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/) + [Ch6 Namespaces](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/) |
| エラーコードの意味が分からない | [Error Explanations](https://lean-lang.org/doc/reference/latest/Error-Explanations/) |
| どのタクティクを使うか迷った | [Ch14.5 Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) — カテゴリ別に探す |
| 基本型の API を知りたい | [Ch20 Basic Types](https://lean-lang.org/doc/reference/latest/Basic-Types/) — 該当する型のページ |
| Lake / ビルドの問題 | [Ch24 Build Tools and Distribution](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/) |

### 参照の優先順位

1. **まず本索引** の逆引きテーブル（セクション3）で該当セクションを特定
2. **Tactic Reference** (Ch14.5) — タクティク関連の疑問は全てここが起点
3. **Basic Types** (Ch20) — 型の API や操作の確認
4. **Error Explanations** — エラーメッセージの解釈
5. **各章の詳細ページ** — 上記で解決しない場合に個別章を参照

### 他のプロジェクト内ガイドとの使い分け

| ガイド | 用途 |
|-------|------|
| 本ドキュメント（リファレンス索引） | Lean 4 の文法・機能の **正確な仕様** を調べたいとき |
| [FP in Lean ガイド](fp-in-lean-guide.md) | 関数型プログラミングの **概念・パターン** を学びたいとき |
| [Theorem Proving ガイド](theorem-proving-guide.md) | 定理証明の **テクニック・ベストプラクティス** を知りたいとき |

---

## 免責事項

本ドキュメントは非公式の索引・要約資料です。Lean プロジェクトおよびその著者とは一切関係がありません。内容の正確さについて一切保証しません。本ドキュメントを参照したことによって生じたいかなる損害についても、作成者は責任を負いません。

## ライセンス・著作権表記

本ドキュメントは以下の著作物を索引化・要約・再編集した派生物であり、Apache License 2.0 に基づいて頒布されます。

**原著作物:**

- 書名: *The Lean Language Reference*
- 著作権者: Copyright Lean FRO, LLC and contributors
- ライセンス: Apache License 2.0
- リポジトリ: <https://github.com/leanprover/reference-manual>
- 公開 URL: <https://lean-lang.org/doc/reference/latest/>

本ドキュメントは原著作物を索引化・要約・再構成したものです。Apache License 2.0 の全文は <https://www.apache.org/licenses/LICENSE-2.0> を参照してください。
