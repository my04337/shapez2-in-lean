# Duper 活用ガイド — S2IL プロジェクト向け

Duper (Deduction Unification Proof Equality Reasoning) のプロジェクト内活用ガイド。
超位置推論（superposition calculus）ベースの自動定理証明器をいつ・どう使うかを整理する。

> **タクティク構文の詳細**: [`docs/lean/tactics/detail/自動化/duper.md`](tactics/detail/自動化/duper.md)（作成予定）
> **Duper 公式リポジトリ**: https://github.com/leanprover-community/duper (Apache 2.0)

---

## 前提

- Duper は **独立した依存** として `lakefile.toml` に直接追加されている（`leanprover-community/duper` v4.29.0）
- Duper は `lean-auto` に依存し、`lean-auto` は `Batteries` に依存する（プロジェクトでは Mathlib 経由で既に利用可能）
- **S2IL REPL ではデフォルト auto-import (`import S2IL + Mathlib.Tactic + Plausible + Duper`) に含まれる**
  - `duper` タクティクは追加 import なしでそのまま使える
- `-NoPickle` モードや S2IL と無関係のスタンドアロンファイルでは `import Duper` が必要
- S2IL の `.lean` ソースファイルで使う場合は `import Duper` をファイル先頭に追加する

---

## Duper とは

Duper は **超位置推論ベースの一階述語論理の自動定理証明器**（Isabelle の Metis / Vampire に類似）。

- 与えられたファクト（仮定・外部補題・定義）から、**一階述語論理の推論**でゴールを閉じる
- `aesop` や `simp` が「書き換え + ルール探索」なのに対し、Duper は「節解消 + 等式推論」で証明を構成
- **terminal tactic**: `duper` が成功すればゴールは即座に閉じる（サブゴールは生まれない）

---

## 基本的な使い方

### 構文

```lean
duper [fact₁, fact₂, ...] {option₁ := val₁, ...}
```

- `[facts]`: ファクトリスト。仮定名・外部補題名・定義名・帰納子を指定
- `{options}`: オプション（省略可）
- ファクトリストも省略可（ターゲットのみで解く）

### ファクトの指定方法

| ファクト | 説明 | 例 |
|---|---|---|
| 仮定名 | ローカルコンテキストの仮定 | `duper [h1, h2]` |
| 外部補題 | Mathlib / Batteries / プロジェクト補題 | `duper [Nat.pos_iff_ne_zero]` |
| 定義名 | `def` の展開（`@[reducible]` 相当） | `duper [MyDef]` |
| `*` | ローカルコンテキストの全仮定 | `duper [*]` |
| （なし） | ターゲットのみ | `duper` |

### 基本例

```lean
-- ローカル仮定のみで論理式を閉じる
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  duper [*]

-- 外部補題を指定して閉じる
example (n : Nat) (h : n > 0) : n ≠ 0 := by
  duper [Nat.pos_iff_ne_zero, h]

-- 推移的推論
example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by
  duper [h1, h2, hp]

-- ファクトなし（ターゲットのみ）
example : True := by
  duper
```

---

## `duper?` — 証明スクリプト生成

`duper?` は成功した場合に **再現可能な proof script** を提案する。

```lean
example (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  duper? [*]
  -- Try this: duper [*] {portfolioInstance := 1}
```

- 出力された `portfolioInstance := n` を使えば、次回以降は同じソルバーインスタンスで高速に再現できる
- **最終証明では `duper?` の出力を `duper` に置換する**（`portfolioInstance` 付き推奨）

---

## オプション

| オプション | デフォルト | 説明 |
|---|---|---|
| `portfolioInstance` | （なし） | 使用するソルバーインスタンス番号 (0-24)。指定すると単一インスタンスで実行 |
| `portfolioMode` | `true` | `true`: 複数インスタンス (3-4) を並列実行。`false`: 単一インスタンス |
| `preprocessing` | `full` | `full` / `monomorphization` / `no_preprocessing` |
| `inhabitationReasoning` | `true` | 型の inhabitability 推論を有効化 |
| `includeExpensiveRules` | `false` | コストの高い推論ルールを含める（タイムアウト時の再試行用） |

### portfolioInstance の活用

```lean
-- 探索時: portfolioMode = true（デフォルト、3-4 インスタンスが並列試行）
example ... := by duper [*]

-- 安定化時: duper? で取得した portfolioInstance を固定
example ... := by duper [*] {portfolioInstance := 1}
```

---

## 良い使い方

### 1. 一階述語論理の推論チェーン

`∀`, `∃`, `→`, `∧`, `∨` で構成される論理式で、`aesop` が到達しないもの。

```lean
-- 複数ステップの推移的推論
example (α : Type) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (a : α) (ha : P a) : Q a := by
  duper [h, ha]
```

### 2. 等式推論の組合せ

等式の推移性・対称性を組み合わせた推論。

```lean
example (c1 c2 : Color) (h : c1 = c2) : c2 = c1 := by
  duper [h]
```

### 3. `aesop` / `simp` が失敗するゴールのフォールバック

`aesop` や `simp` が閉じられないが、与えた仮定から論理的に導出可能なゴール。

### 4. sorry 解消時の探索的使用

```lean
-- sorry を duper [*] で試す → 成功したら duper? で安定化
theorem my_lemma ... := by
  intro h
  duper? [*]  -- Try this: duper [*] {portfolioInstance := 3}
```

---

## 悪い使い方

### 1. 帰納法が必要なゴール

Duper は **帰納法を行わない**。帰納型の構造的性質は `induction` / `cases` を先に使う。

```lean
-- ❌ Duper は帰納法を実行しない
example (l : List Nat) : l.reverse.reverse = l := by duper [*]  -- 失敗

-- ✅ まず induction で分解してから duper を使う
example (l : List Nat) : l.reverse.reverse = l := by
  induction l with
  | nil => duper [*]
  | cons h t ih => simp [List.reverse_cons]; exact ih  -- duper では厳しい
```

### 2. 高階関数を含むゴール

`fun x => ...` や `(· + 1)` 等の高階項が本質的な場合、Duper は弱い。

### 3. ファクトが大量に必要なゴール

Duper は与えたファクトが少ないほど高速。`duper [*]` で仮定が 20 個以上ある場合はタイムアウトしやすい。
→ 必要な仮定だけを選別して渡す。

### 4. 算術ゴール

Nat/Int の算術は `omega` / `linarith` の方が確実。Duper の等式推論では非効率。

### 5. 最終証明で裸の `duper` を使う

`duper [*]` は仮定の変化で壊れうる。最終証明では：
- `duper?` でスクリプトを取得し、`portfolioInstance` 付きに置換する
- または明示的なファクトリスト `duper [h1, h2]` を使う

---

## デバッグ

### トレースオプション

```lean
set_option trace.duper.timeout.debug true      -- タイムアウト原因の診断
set_option trace.duper.saturate.debug true      -- 飽和探索の詳細ログ
set_option trace.duper.printProof true          -- 証明項の出力
set_option trace.duper.proofReconstruction true -- 証明再構成の詳細
set_option trace.duper.monomorphization.debug true -- 単相化の詳細
```

### タイムアウト時の対処

1. **ファクトを減らす**: `duper [*]` → `duper [h1, h2]` のように必要な仮定だけにする
2. **`portfolioMode := false`**: 単一インスタンスで最大ハートビートを使わせる
3. **`includeExpensiveRules := true`**: コストの高い推論ルールを有効化
4. **`preprocessing := monomorphization`**: 前処理を変更してみる
5. **`set_option maxHeartbeats 800000`**: ハートビート数を増やす

---

## 他のタクティクとの比較

| タクティク | 得意分野 | Duper との使い分け |
|---|---|---|
| `aesop` | 構造的ゴール・`@[simp]` + `@[aesop]` ルール探索 | Duper は `aesop` が失敗する一階論理推論に強い |
| `omega` | Nat/Int の線形算術 | 算術は `omega` を優先 |
| `simp` | 等式書き換えチェーン | Duper は複数等式の組合せ推論に強い |
| `decide` | 有限列挙型の全探索 | 小さい有限型は `decide` が確実 |
| `grind` | SMT 風の等式推論 + ケース分割 | Duper は純粋な論理推論、`grind` は SMT ベース |
| `exact?` | ライブラリ補題の一発適用 | Duper は複数補題の組合せ推論ができる |

---

## S2IL プロジェクトでの活用指針

### 推奨されるユースケース

1. **等変性証明の論理推論ステップ**: `rotate180` 等の変換が各操作と可換であることの推論チェーン
2. **sorry 解消の探索**: `duper? [*]` で試行 → 成功したら安定化
3. **`aesop` / `simp_all` の代替**: これらが失敗する場合のフォールバック

### 推奨フロー

```
1. sorry のゴールを確認
2. duper? [*] を試行（REPL で ~15s）
3. 成功 → portfolioInstance 付きに安定化
4. 失敗 → ファクトを選別して duper [h1, h2] を試行
5. それでも失敗 → 別のアプローチ（induction, cases, simp 等）
```

---

## REPL での使い方

REPL のデフォルト環境 (`env: 0`) で `duper` タクティクは即座に利用可能。

```jsonl
{"cmd": "example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  duper [*]", "env": 0}

{"cmd": "example (p q : Prop) (hp : p) (hq : q) : q ∧ p := by\n  duper? [*]", "env": 0}
```

---

## 関連

- **[lean-tactic-select スキル](../../.github/skills/lean-tactic-select/SKILL.md)** — Step 3 フォールバックで `duper` を使用
- **[lean-proof-planning スキル](../../.github/skills/lean-proof-planning/SKILL.md)** — 行き詰まり時の Duper 試行フロー
- **[Aesop 活用ガイド](aesop-guide.md)** — `aesop` との使い分け
