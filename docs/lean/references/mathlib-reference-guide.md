# Mathlib — エージェント向けリファレンス索引

> **出典**: [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
> **Mathlib 概要**: [Mathlib Overview](https://leanprover-community.github.io/mathlib-overview.html)
> Lean バージョン: 4.29.0

本ドキュメントは、Lean 4 用数学ライブラリ **Mathlib** の主要機能・モジュール構成・タクティクをエージェント向けに索引化したリファレンスです。
Mathlib のどこに何があるかを素早く特定し、適切な API ページを参照するための手引きとして活用してください。

---

## 目次

1. [トップレベルモジュール一覧](#1-トップレベルモジュール一覧)
2. [分野別機能索引](#2-分野別機能索引)
3. [Mathlib タクティク一覧（主要）](#3-mathlib-タクティク一覧主要)
4. [逆引きリファレンス — やりたいこと別索引](#4-逆引きリファレンス--やりたいこと別索引)
5. [理解が難しい概念の参照先](#5-理解が難しい概念の参照先)
6. [検索・探索ツール](#6-検索探索ツール)
7. [エージェント向け参照戦略](#7-エージェント向け参照戦略)

---

## 1. トップレベルモジュール一覧

基本URL: `https://leanprover-community.github.io/mathlib4_docs/`

| モジュール | 概要 | URL |
|-----------|------|-----|
| `Mathlib` | Mathlib ルートモジュール | [Mathlib.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html) |
| `Mathlib.Init` | 初期化・基盤 | [Mathlib/Init.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init.html) |
| `Mathlib.Tactic` | タクティク集 | [Mathlib/Tactic.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic.html) |
| `Mathlib.Algebra` | 代数的構造 | [Mathlib/Algebra.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra.html) |
| `Mathlib.Order` | 順序・束 | [Mathlib/Order.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order.html) |
| `Mathlib.Data` | データ構造・基本型 | [Mathlib/Data.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data.html) |
| `Mathlib.Logic` | 論理・集合論的基盤 | [Mathlib/Logic.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic.html) |
| `Mathlib.Topology` | 位相空間論 | [Mathlib/Topology.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology.html) |
| `Mathlib.Analysis` | 解析学 | [Mathlib/Analysis.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis.html) |
| `Mathlib.MeasureTheory` | 測度論・積分 | [Mathlib/MeasureTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory.html) |
| `Mathlib.LinearAlgebra` | 線形代数 | [Mathlib/LinearAlgebra.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra.html) |
| `Mathlib.RingTheory` | 環論 | [Mathlib/RingTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory.html) |
| `Mathlib.FieldTheory` | 体論 | [Mathlib/FieldTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory.html) |
| `Mathlib.GroupTheory` | 群論 | [Mathlib/GroupTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory.html) |
| `Mathlib.NumberTheory` | 数論 | [Mathlib/NumberTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory.html) |
| `Mathlib.CategoryTheory` | 圏論 | [Mathlib/CategoryTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory.html) |
| `Mathlib.Combinatorics` | 組合せ論 | [Mathlib/Combinatorics.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics.html) |
| `Mathlib.Geometry` | 幾何学 | [Mathlib/Geometry.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry.html) |
| `Mathlib.Probability` | 確率論 | [Mathlib/Probability.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability.html) |
| `Mathlib.SetTheory` | 集合論 | [Mathlib/SetTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory.html) |
| `Mathlib.ModelTheory` | モデル論 | [Mathlib/ModelTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory.html) |
| `Mathlib.Computability` | 計算可能性理論 | [Mathlib/Computability.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability.html) |
| `Mathlib.RepresentationTheory` | 表現論 | [Mathlib/RepresentationTheory.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory.html) |
| `Mathlib.Dynamics` | 力学系 | [Mathlib/Dynamics.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics.html) |
| `Batteries` | 標準拡張ライブラリ | [Batteries.html](https://leanprover-community.github.io/mathlib4_docs/Batteries.html) |

---

## 2. 分野別機能索引

> 参照: [Mathlib Overview](https://leanprover-community.github.io/mathlib-overview.html)

### 2.1 一般代数 (General Algebra)

#### 圏論 (Category Theory)

| トピック | 主要な定義・定理 | API URL |
|---------|---------------|---------|
| 圏・関手・自然変換 | `Category`, `Functor`, `NatTrans` | [CategoryTheory/](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory.html) |
| 極限・余極限 | `Limit`, `Colimit` | [CategoryTheory/Limits/](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits.html) |
| アーベル圏 | `Abelian` | [CategoryTheory/Abelian/](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian.html) |
| モノイダル圏 | `MonoidalCategory` | [CategoryTheory/Monoidal/](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monoidal.html) |
| 随伴 | `Adjunction` | [CategoryTheory/Adjunction/](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction.html) |

#### 数の体系 (Numbers)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 自然数 | `Nat` の拡張的性質 | `Mathlib.Data.Nat` |
| 整数 | `Int` | `Mathlib.Data.Int` |
| 有理数 | `Rat`, `ℚ` | `Mathlib.Data.Rat` |
| 実数 | `Real`, `ℝ` (Cauchy 列による構成) | `Mathlib.Topology.Instances.Real` |
| 複素数 | `Complex`, `ℂ` | `Mathlib.Analysis.SpecialFunctions.Complex` |
| p 進数 | `Padic`, `ℚ_[p]` | `Mathlib.NumberTheory.Padics` |
| 基数・順序数 | `Cardinal`, `Ordinal` | `Mathlib.SetTheory.Cardinal`, `Mathlib.SetTheory.Ordinal` |

#### 群論 (Group Theory)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 群・部分群 | `Group`, `Subgroup` | `Mathlib.Algebra.Group`, `Mathlib.GroupTheory.Subgroup` |
| 群準同型 | `MonoidHom` | `Mathlib.Algebra.Group.Hom` |
| 群の作用 | `MulAction` | `Mathlib.Algebra.Group.Action` |
| Sylow の定理 | `Sylow` | `Mathlib.GroupTheory.Sylow` |
| 自由群 | `FreeGroup` | `Mathlib.GroupTheory.FreeGroup` |
| アーベル化 | `Abelianization` | `Mathlib.GroupTheory.Abelianization` |

#### 環論 (Ring Theory)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 環・可換環 | `Ring`, `CommRing` | `Mathlib.Algebra.Ring` |
| イデアル | `Ideal` | `Mathlib.RingTheory.Ideal` |
| 商環 | `Ideal.Quotient` | `Mathlib.RingTheory.Ideal.Quotient` |
| 局所化 | `Localization` | `Mathlib.RingTheory.Localization` |
| 多項式環 | `Polynomial`, `MvPolynomial` | `Mathlib.RingTheory.Polynomial` |
| 行列環 | `Matrix` | `Mathlib.Data.Matrix` |
| Noether 環 | `IsNoetherianRing` | `Mathlib.RingTheory.Noetherian` |

#### 体論 (Field Theory)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 体拡大 | `IntermediateField` | `Mathlib.FieldTheory.IntermediateField` |
| Galois 理論 | `IsGalois` | `Mathlib.FieldTheory.Galois` |
| 分離拡大 | `IsSeparable` | `Mathlib.FieldTheory.Separable` |
| 有限体 | `GaloisField` | `Mathlib.FieldTheory.Finite` |

#### 整数論 (Number Theory)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 素数 | `Nat.Prime` | `Mathlib.Data.Nat.Prime` |
| 二次互恵法則 | `legendreSym.quadratic_reciprocity` | `Mathlib.NumberTheory.LegendreSymbol` |
| Bernoulli 数 | `bernoulli` | `Mathlib.NumberTheory.Bernoulli` |
| 代数的整数 | `NumberField`, `RingOfIntegers` | `Mathlib.NumberTheory.NumberField` |

### 2.2 線形代数 (Linear Algebra)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 加群・線形写像 | `Module`, `LinearMap` | `Mathlib.Algebra.Module`, `Mathlib.LinearAlgebra` |
| 双対空間 | `Module.Dual` | `Mathlib.LinearAlgebra.Dual` |
| 有限次元 | `FiniteDimensional` | `Mathlib.LinearAlgebra.FiniteDimensional` |
| 行列 | `Matrix` | `Mathlib.Data.Matrix` |
| 行列式 | `Matrix.det` | `Mathlib.LinearAlgebra.Matrix.Determinant` |
| 固有値・固有空間 | `Module.End.eigenspace` | `Mathlib.LinearAlgebra.Eigenspace` |
| 双線形形式 | `BilinForm` | `Mathlib.LinearAlgebra.BilinearForm` |
| 二次形式 | `QuadraticForm` | `Mathlib.LinearAlgebra.QuadraticForm` |
| テンソル積 | `TensorProduct` | `Mathlib.LinearAlgebra.TensorProduct` |

### 2.3 位相空間論 (Topology)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| フィルタ | `Filter` | `Mathlib.Order.Filter` |
| 位相空間 | `TopologicalSpace` | `Mathlib.Topology.Defs` |
| 連続写像 | `Continuous` | `Mathlib.Topology.Defs.Basic` |
| コンパクト性 | `IsCompact` | `Mathlib.Topology.Compactness` |
| 連結性 | `IsConnected` | `Mathlib.Topology.Connected` |
| 一様空間 | `UniformSpace` | `Mathlib.Topology.UniformSpace` |
| 距離空間 | `MetricSpace`, `PseudoMetricSpace` | `Mathlib.Topology.MetricSpace` |
| 位相群 | `TopologicalGroup` | `Mathlib.Topology.Algebra.Group` |
| 位相環 | `TopologicalRing` | `Mathlib.Topology.Algebra.Ring` |

### 2.4 解析学 (Analysis)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| ノルム空間 | `NormedAddCommGroup`, `NormedSpace` | `Mathlib.Analysis.Normed.Group`, `Mathlib.Analysis.Normed.Module` |
| Banach 空間 | 完備ノルム空間 | `Mathlib.Analysis.Normed.Module` |
| Hilbert 空間 | `InnerProductSpace` | `Mathlib.Analysis.InnerProductSpace` |
| 微分 | `HasDerivAt`, `HasFDerivAt` | `Mathlib.Analysis.Calculus.Deriv`, `Mathlib.Analysis.Calculus.FDeriv` |
| 積分 (Bochner) | `MeasureTheory.integral` (`∫`) | `Mathlib.MeasureTheory.Integral.Bochner` |
| 測度 | `MeasureTheory.Measure` | `Mathlib.MeasureTheory.Measure` |
| Lebesgue 測度 | `MeasureTheory.volume` | `Mathlib.MeasureTheory.Measure.Lebesgue` |
| 凸性 | `Convex` | `Mathlib.Analysis.Convex` |
| 特殊関数 (`exp`, `log`, `sin`, `cos`) | `Real.exp`, `Real.log`, `Real.sin` | `Mathlib.Analysis.SpecialFunctions` |
| 複素解析 | `DifferentiableAt` (ℂ 上) | `Mathlib.Analysis.Complex` |
| Fourier 解析 | `fourierCoeff` | `Mathlib.Analysis.Fourier` |

### 2.5 確率論 (Probability Theory)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 確率測度 | `MeasureTheory.IsProbabilityMeasure` | `Mathlib.Probability.ProbabilityMassFunction` |
| 条件付き期待値 | `MeasureTheory.condexp` | `Mathlib.Probability.ConditionalExpectation` |
| 独立性 | `ProbabilityTheory.IndepFun` | `Mathlib.Probability.Independence` |

### 2.6 幾何学 (Geometry)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| アフィン空間 | `AffineSpace` | `Mathlib.LinearAlgebra.AffineSpace` |
| Euclid 幾何 | `EuclideanGeometry` | `Mathlib.Geometry.Euclidean` |
| 多様体 | `SmoothManifoldWithCorners` | `Mathlib.Geometry.Manifold` |
| 代数幾何 | `PrimeSpectrum`, `Scheme` | `Mathlib.AlgebraicGeometry` |
| 凸幾何 | `Convex`, `ConvexHull` | `Mathlib.Analysis.Convex` |

### 2.7 組合せ論 (Combinatorics)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 鳩ノ巣原理 | `Fintype.exists_ne_map_eq_of_card_lt` | `Mathlib.Combinatorics.Pigeonhole` |
| グラフ理論 | `SimpleGraph` | `Mathlib.Combinatorics.SimpleGraph` |
| 列挙的組合せ | `Nat.choose` | `Mathlib.Data.Nat.Choose` |
| 集合族 | `SetFamily` | `Mathlib.Combinatorics.SetFamily` |
| 加法的組合せ論 | `Finset.addConst_card_le_card_add` | `Mathlib.Combinatorics.Additive` |
| マトロイド | `Matroid` | `Mathlib.Combinatorics.Matroid` |

### 2.8 力学系 (Dynamics)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 周期点 | `Function.IsPeriodicPt` | `Mathlib.Dynamics.PeriodicPts` |
| エルゴード理論 | `MeasureTheory.Ergodic` | `Mathlib.Dynamics.Ergodic` |

### 2.9 データ構造 (Data Structures)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| リスト | `List` の拡張 | `Mathlib.Data.List` |
| 有限集合 | `Finset` | `Mathlib.Data.Finset` |
| 多重集合 | `Multiset` | `Mathlib.Data.Multiset` |
| 有限マップ | `Finmap` | `Mathlib.Data.Finmap` |
| ベクタ | `Mathlib.Data.Vector` | `Mathlib.Data.Vector` |

### 2.10 論理と計算 (Logic and Computation)

| トピック | 主要な定義・定理 | モジュール |
|---------|---------------|----------|
| 計算可能性 | `Computable`, `Primrec` | `Mathlib.Computability` |
| 形式言語 | `Language` | `Mathlib.Computability.Language` |
| 集合論 | `ZFSet`, `PGame` | `Mathlib.SetTheory` |
| モデル論 | `FirstOrder.Language` | `Mathlib.ModelTheory` |

---

## 3. Mathlib タクティク一覧（主要）

> 完全なリスト: [Tactics](https://leanprover-community.github.io/mathlib4_docs/tactics.html)

### 自動証明・決定手続き

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `aesop` | ルールベースの自動証明（`@[aesop]` 属性） | `Aesop.Frontend.Tactic` |
| `grind` | SMT 風の自動証明（等式推論・E マッチング・LIA・環ソルバー統合） | `Init.Grind.Tactics` |
| `decide` | `Decidable` な命題を自動判定 | `Init.Tactics` |
| `norm_num` | 数値式を正規化して評価（素数判定も可能） | `Mathlib.Tactic.NormNum` |
| `omega` | 自然数・整数の線形算術 | `Init.Tactics` |
| `lia` | 線形整数算術（`grind` ラッパー） | `Init.Grind.Tactics` |
| `bv_decide` | ビットベクタの SAT ソルバー | `Std.Tactic.BVDecide` |
| `itauto` | 直観主義命題論理のタクティク（完全） | `Mathlib.Tactic.ITauto` |
| `tauto` | 命題のトートロジーを自動証明 | `Mathlib.Tactic.Tauto` |
| `plausible` | 反例探索（テストベース） | `Plausible.Tactic` |

### 代数的証明

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `ring` | 可換環の等式を自動証明 | `Mathlib.Tactic.Ring` |
| `ring_nf` | 環の式を正規形に変換 | `Mathlib.Tactic.Ring` |
| `noncomm_ring` | 非可換環の等式 | `Mathlib.Tactic.NoncommRing` |
| `group` | 群の等式 | `Mathlib.Tactic.Group` |
| `abel` | アーベル群の等式 | `Mathlib.Tactic.Abel` |
| `module` | 加群のスカラー等式 | `Mathlib.Tactic.Module` |
| `field` | 体の等式（非零条件を自動放電） | `Mathlib.Tactic.Field` |
| `field_simp` | 体の分数を消去して簡約 | `Mathlib.Tactic.FieldSimp` |
| `linear_combination` | 線形結合を用いた等式・不等式証明 | `Mathlib.Tactic.LinearCombination` |

### 不等式・順序

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `positivity` | `0 ≤ x`, `0 < x`, `x ≠ 0` を再帰的に証明 | `Mathlib.Tactic.Positivity` |
| `linarith` | 線形算術の不等式（仮定を線形結合） | `Mathlib.Tactic.Linarith` |
| `nlinarith` | 非線形算術の不等式（`linarith` の拡張） | `Mathlib.Tactic.Linarith` |
| `order` | 半順序・全順序のゴール | `Mathlib.Tactic.Order` |
| `gcongr` | 合同な不等式（`a ≤ b → f a ≤ f b` 的推論） | `Mathlib.Tactic.GCongr` |
| `bound` | 限界に関する証明 | `Mathlib.Tactic.Bound` |

### 簡約・書き換え

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `simp` | 自動簡約（`@[simp]` 補題を適用） | `Init.Tactics` |
| `norm_cast` | キャスト（型変換）の正規化 | `Init.Tactics` |
| `push_cast` | キャストを内側に押し込む | `Init.Tactics` |
| `push_neg` | 否定を内側に押し込む (`¬ ∀` → `∃ ¬` 等) | `Mathlib.Tactic.PushNeg` |
| `push` / `pull` | 一般的な記号の内側/外側への移動 | `Mathlib.Tactic.Push` |
| `reduce_mod_char` | 正標数における数値式の簡約 | `Mathlib.Tactic.ReduceModChar` |

### 解析・位相

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `continuity` | `Continuous f` を自動証明 | `Mathlib.Tactic.Continuity` |
| `measurability` | `Measurable f` を自動証明 | `Mathlib.Tactic.Measurability` |
| `fun_prop` | 関数の性質 (`Continuous`, `Differentiable` 等) を自動証明 | `Mathlib.Tactic.FunProp` |
| `finiteness` | `*** < ∞` や `*** ≠ ∞` (ENNReal) を証明 | `Mathlib.Tactic.Finiteness` |
| `filter_upwards` | フィルタのメンバーシップ目標を変換 | `Mathlib.Tactic.FilterUpwards` |
| `borelize` | Borel σ-代数インスタンスを導入 | `Mathlib.MeasureTheory.Constructions.BorelSpace` |

### 構造分析

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `ext` | 外延性（`@[ext]` 補題を適用） | `Init.Ext` |
| `congr!` | 深い合同律の適用（`congr` の強化版） | `Mathlib.Tactic.CongrExclamation` |
| `convert` / `convert_to` | ゴールの型を `congr!` で変換 | `Mathlib.Tactic.Convert` |
| `choose` | 選択公理の適用（`∀ x, ∃ y, P x y` → 関数を抽出） | `Mathlib.Tactic.Choose` |
| `lift` | 部分型へのリフト（例: `ℤ` → `ℕ`、条件付き） | `Mathlib.Tactic.Lift` |
| `obtain` | `have` + `rcases`（仮定をデストラクチャ） | `Init.RCases` |
| `rcases` / `rintro` | 再帰的パターンマッチ付きケース分析・導入 | `Init.RCases` |
| `peel` | 量化子を一枚ずつ剥がす | `Mathlib.Tactic.Peel` |

### 数値変換

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `zify` | `ℕ` の命題を `ℤ` に変換 | `Mathlib.Tactic.Zify` |
| `qify` | `ℕ` / `ℤ` の命題を `ℚ` に変換 | `Mathlib.Tactic.Qify` |
| `rify` | `ℕ` / `ℤ` / `ℚ` の命題を `ℝ` に変換 | `Mathlib.Tactic.Rify` |
| `mod_cases` | 剰余によるケース分析 | `Mathlib.Tactic.ModCases` |

### 場合分け・帰納法

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `by_contra` / `by_contra!` | 背理法（否定を仮定に追加） | `Batteries.Tactic.Init` |
| `by_cases` / `by_cases!` | 排中律による場合分け | `Init.ByCases` |
| `contrapose` / `contrapose!` | 対偶を取る | `Mathlib.Tactic.Contrapose` |
| `interval_cases` | 有界な変数の全ケースを列挙 | `Mathlib.Tactic.IntervalCases` |
| `fin_cases` | `Fin n` 等の有限型で全ケース列挙 | `Mathlib.Tactic.FinCases` |
| `induction'` | 後方互換な帰納法（Lean 3 スタイル） | `Mathlib.Tactic.Induction` |
| `wlog` | 一般性を損なわずに仮定を追加 | `Mathlib.Tactic.WLOG` |

### TFAE (The Following Are Equivalent)

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `tfae_have` | TFAE の含意を追加 | `Mathlib.Tactic.TFAE` |
| `tfae_finish` | TFAE を完了 | `Mathlib.Tactic.TFAE` |

### デバッグ・探索

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `exact?` | ゴールを閉じる補題を自動検索 | `Init.Tactics` |
| `apply?` | 適用可能な補題を検索 | `Init.Tactics` |
| `rw?` | 使える書き換え規則を検索 | `Init.Tactics` |
| `#find` | 型シグネチャで定義・定理を検索 | `Mathlib.Tactic.Find` |
| `#loogle` | [Loogle](https://loogle.lean-lang.org/) で検索 | `LeanSearchClient.LoogleSyntax` |
| `#leansearch` | [LeanSearch](https://leansearch.net/) で自然言語検索 | `LeanSearchClient` |
| `hint` | 登録されたヒント戦略を試す | `Mathlib.Tactic.Hint` |
| `observe` / `observe?` | `exact?` で仮定を追加 | `Mathlib.Tactic.Observe` |
| `linarith?` | `linarith` の最小化バージョン（使用した仮定を出力） | `Mathlib.Tactic.Linarith` |

### 圏論専用

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `aesop_cat` | 圏論向け `aesop`（`CategoryTheory` ルールセット） | `Mathlib.CategoryTheory.Category.Basic` |
| `coherence` | モノイダル圏の coherence | `Mathlib.Tactic.CategoryTheory.Coherence` |
| `slice_lhs` / `slice_rhs` | 射の合成のスライス | `Mathlib.Tactic.CategoryTheory.Slice` |

### その他の便利なタクティク

| タクティク | 用途 | 定義元 |
|-----------|------|--------|
| `set` | ローカル定義を導入して置換 | `Mathlib.Tactic.Set` |
| `swap_var` | 変数名を入れ替え | `Mathlib.Tactic.SwapVar` |
| `clear_value` | let 束縛の値を消去 | `Init.Tactics` |
| `split_ifs` | 全 `if-then-else` を場合分け | `Mathlib.Tactic.SplitIfs` |
| `compute_degree` | 多項式の次数計算 | `Mathlib.Tactic.ComputeDegree` |
| `says` | タクティクの出力を記録 | `Mathlib.Tactic.Says` |
| `nontriviality` | 自明でない型の仮定を導入 | `Mathlib.Tactic.Nontriviality` |
| `show_term` | タクティクが生成した項を表示 | `Init.Tactics` |

---

## 4. 逆引きリファレンス — やりたいこと別索引

### 数式の証明

| やりたいこと | 使うタクティク | 補足 |
|------------|-------------|------|
| 可換環の等式を証明したい | `ring` | 整数・有理数・多項式等に対応 |
| 非可換環の等式を証明したい | `noncomm_ring` | |
| 体の等式を証明したい（分数あり） | `field` または `field_simp` + `ring` | `field_simp` で分数を消去 → `ring` |
| 群の等式を証明したい | `group` | |
| アーベル群の等式を証明したい | `abel` | |
| 加群の等式を証明したい | `module` | スカラー部分は `match_scalars` |
| 線形結合で等式を示したい | `linear_combination` | 仮定の線形結合を指定 |

### 不等式の証明

| やりたいこと | 使うタクティク | 補足 |
|------------|-------------|------|
| `0 ≤ x` / `0 < x` / `x ≠ 0` を示したい | `positivity` | 再帰的に分解して証明 |
| 線形不等式を示したい | `linarith` | 仮定の線形結合で導出 |
| 非線形不等式を示したい | `nlinarith` | 二乗項を追加して `linarith` |
| 自然数・整数の算術的命題 | `omega` | 量化子なしの線形算術 |
| 順序関係のゴール | `order` | `Preorder`, `PartialOrder`, `LinearOrder` |
| 単調性を使った不等式 (`a ≤ b → f a ≤ f b`) | `gcongr` | `@[gcongr]` 補題を利用 |

### 型変換・キャスト

| やりたいこと | 使うタクティク | 補足 |
|------------|-------------|------|
| `ℕ` → `ℤ` に変換したい | `zify` | 仮定・ゴールの型を変換 |
| `ℕ` / `ℤ` → `ℚ` に変換したい | `qify` | |
| `ℕ` / `ℤ` / `ℚ` → `ℝ` に変換したい | `rify` | |
| キャストを正規化したい | `norm_cast` / `push_cast` | |
| 部分型にリフトしたい | `lift` | 例: `lift (z : ℤ) to ℕ` |

### 位相・解析の性質

| やりたいこと | 使うタクティク | 補足 |
|------------|-------------|------|
| 関数の連続性を示したい | `continuity` または `fun_prop` | `fun_prop` の方が新しく強力 |
| 関数の可測性を示したい | `measurability` | `@[measurability]` 補題 |
| 関数の性質を汎用的に示したい | `fun_prop` | `Continuous`, `Differentiable` 等を統合 |
| `*** < ∞` (ENNReal) を示したい | `finiteness` | |
| フィルタのメンバーシップ | `filter_upwards` | |

### 探索・発見

| やりたいこと | 使うツール | 補足 |
|------------|----------|------|
| ゴールを閉じる補題を見つけたい | `exact?` | ライブラリ全体を検索 |
| 適用可能な補題を見つけたい | `apply?` | |
| 書き換え規則を見つけたい | `rw?` | |
| 型シグネチャで定理を検索したい | `#find` / `#loogle` | Loogle はパターンマッチ |
| 自然言語で定理を検索したい | `#leansearch` | LeanSearch API を利用 |
| 反例を見つけたい | `plausible` | ランダムテスト |

### 構造的な操作

| やりたいこと | 使うタクティク | 補足 |
|------------|-------------|------|
| 選択関数を抽出したい | `choose` | `∀ x, ∃ y, ...` → 関数 |
| WLOG パターンで証明したい | `wlog` | 対称性を利用 |
| TFAE を証明したい | `tfae_have` + `tfae_finish` | |
| 否定を内側に動かしたい | `push_neg` | |
| 有界な変数で全ケース試したい | `interval_cases` | 上下界を自動検出 |
| 有限型で全ケース試したい | `fin_cases` | `Fin n`, `Bool` 等 |
| 正の標数で数値を簡約したい | `reduce_mod_char` | `ZMod n` 等 |

---

## 5. 理解が難しい概念の参照先

### Mathlib の型クラス階層

- **参照先**: [Mathlib.Algebra.Group.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html), [Mathlib.Algebra.Ring.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html)
- **ポイント**: Mathlib は `Monoid` → `Group` → `Ring` → `Field` のような精密な型クラス階層を持つ。加法構造と乗法構造が別々に定義されている（`AddGroup`, `MulGroup`）。`instance` 合成が深くなりがちなので、明示的な型注釈が必要な場面がある。

### Bundled vs Unbundled 準同型

- **参照先**: [Mathlib.Algebra.Group.Hom.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Hom/Defs.html)
- **ポイント**: Mathlib では準同型を構造体として「束ねる」（bundled）方式を採用。例: `MonoidHom` (`→*`), `RingHom` (`→+*`)。関数 `f : A → B` と「`f` は準同型である」という証明をセットにして持つ。

### `Finset` vs `Set` vs `Multiset`

- **参照先**: [Mathlib.Data.Finset.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html), [Mathlib.Data.Set.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html)
- **ポイント**: `Set α` は述語 (`α → Prop`)。`Finset α` は重複なし・順序なしの有限集合（計算可能）。`Multiset α` は重複あり・順序なしの有限集合。用途に応じて使い分ける。

### Filter（フィルタ）

- **参照先**: [Mathlib.Order.Filter.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Basic.html)
- **ポイント**: Mathlib の位相空間論・解析学の基盤概念。「近傍」「極限」「概収束」等を統一的に扱う。`Filter.Eventually` (`∀ᶠ x in f, P x`) と `Filter.Tendsto` がよく使われる。

### `simp` の `@[simp]` 補題の管理

- **参照先**: [The Simplifier](https://lean-lang.org/doc/reference/latest/The-Simplifier/)
- **ポイント**: Mathlib は大量の `@[simp]` 補題を持つ。`simp only [...]` で明示的に指定すると再現性が高い。`simp?` で使われた補題を表示できる。

### `norm_cast` と型強制

- **参照先**: [Mathlib.Tactic.NormCast](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormCast.html)
- **ポイント**: `ℕ ↪ ℤ ↪ ℚ ↪ ℝ` のようなキャスト鎖を正規化する。`@[norm_cast]` / `@[push_cast]` 属性で補題を管理。`assumption_mod_cast`, `exact_mod_cast` も関連。

### `ENNReal` (`ℝ≥0∞`) と `NNReal` (`ℝ≥0`)

- **参照先**: [Mathlib.Topology.Instances.ENNReal](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Instances/ENNReal.html)
- **ポイント**: 測度論では `[0, ∞]` を値域とする `ENNReal` が頻出。`NNReal` は `[0, ∞)` で `ℝ` の部分型。減算が非標準（`a - b = 0` if `a ≤ b`）なので注意。

---

## 6. 検索・探索ツール

### オンライン検索

| ツール | URL | 概要 |
|-------|-----|------|
| Mathlib4 Docs | https://leanprover-community.github.io/mathlib4_docs/ | API ドキュメント |
| Loogle | https://loogle.lean-lang.org/ | 型パターンによる定理検索 |
| LeanSearch | https://leansearch.net/ | 自然言語による定理検索 |
| Mathlib Overview | https://leanprover-community.github.io/mathlib-overview.html | 分野別の概要ページ |

### Lean 内の検索コマンド・タクティク

| コマンド/タクティク | 用途 |
|-------------------|------|
| `#check` | 定義の型を確認 |
| `#print` | 定義の詳細を表示 |
| `#find` | 型パターンで検索（Lean 内） |
| `#loogle` | Loogle を Lean 内から利用 |
| `#leansearch` | LeanSearch を Lean 内から利用 |
| `exact?` | ゴールを閉じる補題を探索 |
| `apply?` | 適用可能な補題を探索 |
| `rw?` | 使える書き換え規則を探索 |

### Loogle の検索パターン例

| パターン | 意味 |
|---------|------|
| `Real.sin` | `Real.sin` に言及する全補題 |
| `"differ"` | 名前に "differ" を含む全補題 |
| `_ * (_ ^ _)` | 積と冪を含む式のパターン |
| `(?a -> ?b) -> List ?a -> List ?b` | `List.map` のような型シグネチャ |
| `|- tsum _ = _ * tsum _` | 結論の形で検索 |

---

## 7. エージェント向け参照戦略

### いつ何を参照すべきか

| 状況 | 最初に参照すべき箇所 |
|------|-------------------|
| Mathlib にある定理を探したい | `#loogle` / `#leansearch` / `exact?` |
| 代数的等式を証明したい | `ring`, `abel`, `group`, `field` — セクション 3「代数的証明」 |
| 不等式を証明したい | `linarith`, `positivity`, `nlinarith` — セクション 3「不等式・順序」 |
| 型のキャストが煩わしい | `norm_cast`, `push_cast`, `zify`/`qify`/`rify` — セクション 3「数値変換」 |
| 連続性・可測性を示したい | `fun_prop`, `continuity`, `measurability` — セクション 3「解析・位相」 |
| 特定の数学分野の定義を探したい | セクション 2 の分野別索引 → Mathlib Overview |
| タクティクが失敗して原因不明 | `?` バリアント（`simp?`, `linarith?`, `aesop?`）で使われた補題を確認 |
| `simp` の結果が予想外 | `simp?` で適用された補題を確認 → `simp only [...]` に書き換え |
| `instance` が見つからない | `#check` で型クラスインスタンスの存在確認 → `import` 漏れの可能性 |
| Mathlib の命名規則を知りたい | [Naming conventions](https://leanprover-community.github.io/contribute/naming.html) |

### 参照の優先順位

1. **まず本索引** のセクション 4（逆引き）で適切なタクティク/機能を特定
2. **タクティク一覧**（セクション 3）で使い方を確認
3. **分野別索引**（セクション 2）で関連モジュールを特定
4. **Mathlib4 Docs** の個別 API ページで詳細を確認
5. **Loogle / LeanSearch** で具体的な定理を検索

### 他のプロジェクト内ガイドとの使い分け

| ガイド | 用途 |
|-------|------|
| 本ドキュメント（Mathlib リファレンス索引） | Mathlib の **機能・タクティク・API** を調べたいとき |
| [Lean リファレンス索引](lean-reference-guide.md) | Lean 4 **言語仕様** を調べたいとき |
| [FP in Lean ガイド](fp-in-lean-guide.md) | Lean の **関数型プログラミング概念** を学びたいとき |
| [Theorem Proving ガイド](theorem-proving-guide.md) | **定理証明のテクニック** を知りたいとき |
| [数学用語辞書](math-glossary.md) | 数学用語の意味を調べたいとき |

---

## 免責事項

本ドキュメントは非公式の索引・要約資料です。Mathlib プロジェクト、Lean FRO、およびその著者・コントリビュータとは一切関係がありません。内容の正確さについて一切保証しません。本ドキュメントを参照したことによって生じたいかなる損害についても、作成者は責任を負いません。

## ライセンス・著作権表記

本ドキュメントは以下の著作物を索引化・要約・再編集した派生物であり、Apache License 2.0 に基づいて頒布されます。

**原著作物:**

- 名称: *Mathlib* (mathlib4)
- 著作権者: Copyright © The mathlib Community
- ライセンス: Apache License 2.0
- リポジトリ: <https://github.com/leanprover-community/mathlib4>

**引用情報:**

> The mathlib Community. *The Lean Mathematical Library.* In Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP '20), 2020.

**Mathlib ウェブサイト:**

- URL: <https://leanprover-community.github.io/>
- ウェブサイトのライセンス: MIT License
