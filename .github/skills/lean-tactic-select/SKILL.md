---
name: lean-tactic-select
description: >
  Lean 4 の証明ゴールを分類し、試すべきタクティクの優先リストを提示する。
  ゴール形状（等式・算術・帰納型・論理結合子等）に基づき第1候補・第2候補・代替を返す。
  Use when: which tactic, tactic selection, goal analysis, what tactic to use, stuck on goal,
  tactic advice, proof step, next tactic, tactic recommendation, goal shape, choose tactic,
  tactic for equality, tactic for induction, tactic for arithmetic.
metadata:
  argument-hint: 'ゴール形状からタクティク候補を提示します'
---

# タクティク選択スキル

sorry のゴール状態を見て「次に何を打つか」を即答する。

> 詳細なタクティク情報は [`docs/lean/tactics/index.md`](../../../docs/lean/tactics/index.md) を参照。
> 各タクティクの構文・オプション・コードサンプルは `docs/lean/tactics/detail/<カテゴリ>/` 以下。

---

## Step 1: ゴール形状の分類

ゴール `⊢ P` の形状を以下のカテゴリに分類する:

| 分類 | 形状 | 判定基準 |
|---|---|---|
| **等式** | `⊢ a = b` | トップレベルが `=` |
| **線形算術** | `⊢ a < b`, `⊢ a ≤ b` (Nat/Int) | Nat/Int の線形不等式・等式 |
| **非線形算術** | `⊢ a * b ≤ c ^ 2` | 非線形項を含む算術 |
| **環式** | `⊢ a * b + c = d * e` | CommSemiring 等の環上の等式 |
| **∀ / →** | `⊢ ∀ x, P x` / `⊢ A → B` | 全称量化または含意 |
| **∃** | `⊢ ∃ x, P x` | 存在量化 |
| **∧** | `⊢ A ∧ B` | 論理積 |
| **∨** | `⊢ A ∨ B` | 論理和 |
| **帰納型** | `⊢ P (C args)` | ケース分析 / 帰納法を要する |
| **仮定依存** | 仮定に対応する型あり | `exact h` / `apply h` で閉じ得る |
| **False** | `⊢ False` / 矛盾仮定 | 背理法・矛盾で閉じる |
| **Decidable** | `P` が `Decidable` | `decide` / `native_decide` |
| **キャスト** | `↑`, `↓` を含む式 | キャスト正規化 |
| **関数等式** | `⊢ f = g` | 関数の外延的等価 |

---

## Step 2: タクティク優先マップ

### 等式 `⊢ a = b`

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `rfl` | 定義的に等しい場合 |
| 2nd | `ring` | 環上の式（+, *, ^） |
| 3rd | `omega` | Nat/Int の線形等式 |
| 4th | `simp only [lemmas]` | simp 補題で成立 |
| 5th | `norm_num` | 具体的数値計算 |
| alt | `rw [lemma]` → サブゴール | 段階的書き換え |
| alt | `calc` | 複数ステップの推移的変形 |

### 線形算術 (Nat/Int)

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `omega` | Nat/Int の線形不等式・等式 |
| 2nd | `linarith` | ℚ/ℝ の線形不等式 |
| 3rd | `norm_num` | 具体的数値の比較 |
| alt | `simp only [...]` + `omega` | 定義展開後に算術で閉じる |

### 非線形算術

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `nlinarith` | 非線形不等式（ヒント付き） |
| 2nd | `polyrith` | 多項式算術（外部 CAS） |
| alt | `ring_nf` → `linarith` | 正規化後に線形化 |

### 環式 (CommSemiring 等)

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `ring` | 等式の決定 |
| 2nd | `field_simp` → `ring` | 分母を含む場合 |
| 3rd | `ring_nf` | 正規化のみ（閉じない）→ 他と組合せ |
| alt | `linear_combination e` | 仮定の線形結合で等式 |

### ∀ / → (全称量化・含意)

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `intro x` / `intro h` | 1つずつ名前付き導入 |
| 2nd | `intros` | 全部一度に導入 |
| 3rd | `rintro ⟨a, b⟩` | 導入と同時に構造分解 |
| then | 導入後、残ゴールを再分類 | |

### ∃ (存在量化)

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `use witness` | witness が分かっている場合 |
| 2nd | `refine ⟨?_, ?_⟩` | witness と証明を個別に |
| 3rd | `exists witness` | core の存在導入 |
| alt | `constructor` | Sigma / Subtype 系 |

### ∧ (論理積)

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `constructor` | 左右に分解 |
| 2nd | `exact ⟨proof_a, proof_b⟩` | 両方が即座に閉じる場合 |
| 3rd | `refine ⟨?_, ?_⟩` | 個別にサブゴール化 |

### ∨ (論理和)

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `left` / `right` | どちら側を証明するか判明 |
| alt | `by_cases h : P` | 場合分けで一方を選ぶ |

### 帰納型のケース分析・帰納法

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `cases x` | 単純なケース分析 |
| 2nd | `rcases x with ...` | パターン指定付き分解 |
| 3rd | `induction x with ...` | 帰納法（再帰的構造） |
| 4th | `cases x <;> simp [...]` | 全ケースが simp で閉じる場合 |
| alt | `match x with ...` | term-mode パターンマッチ |

### 仮定依存（仮定にマッチ候補あり）

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `exact h` | 仮定がゴールと完全一致 |
| 2nd | `assumption` | 自動で一致する仮定を検索 |
| 3rd | `apply h` | 仮定の結論がゴールにマッチ |
| 4th | `specialize h arg` | 仮定を具体化してから適用 |

### False / 矛盾

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `contradiction` | 仮定に矛盾がある場合 |
| 2nd | `omega` | Nat/Int の矛盾 |
| 3rd | `simp_all` | simp で仮定が False に簡約 |
| alt | `exfalso` → 矛盾を導出 | ゴールを ⊢ False に変換 |

### Decidable

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `decide` | 小サイズの Decidable 命題 |
| 2nd | `native_decide` | 大サイズ（コンパイラ使用） |
| alt | `bv_decide` | BitVec 特化 |

### キャスト混在

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `norm_cast` | キャスト正規化 |
| 2nd | `push_cast` | キャストを葉に向けて移動 |
| 3rd | `zify` / `qify` / `rify` | 型の統一 |
| then | `ring` / `omega` 等で閉じる | |

### 関数等式 `⊢ f = g`

| 優先度 | タクティク | 条件 |
|---|---|---|
| 1st | `funext x` | 関数外延性 |
| 2nd | `ext x` | `@[ext]` 属性付き型 |
| then | 引数に対するゴールを再分類 | |

---

## Step 3: 全分類失敗時のフォールバック

```
1. exact?   — 仮定・ライブラリから候補を検索
2. aesop    — ルールベース自動証明
3. grind    — SMT 風自動証明
4. simp_all — 全仮定+ゴールを一括簡約
5. sorry    — 一時スキップして骨格を確立
```

> **補題名が不明な場合**: `exact?` で見つからなければ **lean-mathlib-search** スキル（または **lean-lemma-finder** エージェント）で `#leansearch` / `#loogle` を含む段階的検索を実行する。

---

## Step 4: REPL でのタクティク試行

REPL スクリプトが `import S2IL + Mathlib.Tactic` を自動プレペンドするため、JSONL 内では `"env": 0` を直接使える。
ring, linarith, nlinarith, exact?, funext, simp? 等すべての Mathlib タクティクが利用可能。

```jsonl
{"cmd": "theorem my_thm (h : n > 5) : n ≥ 6 := by sorry", "env": 0}

{"tactic": "simp", "proofState": 0}

{"tactic": "omega", "proofState": 0}

{"tactic": "ring", "proofState": 0}

{"tactic": "decide", "proofState": 0}
```

- `goals: []` → 証明完了（そのタクティクを採用）
- `goals` にゴール文字列あり → サブゴールが残る（部分的進展）
- `messages[].severity == "error"` → そのタクティクは不適用

---

## Gotchas

- `simp` は探索用。最終証明では `simp?` で補題リストを取得し `simp only [...]` に置換する
- `omega` は Nat/Int 専用。ℝ/ℚ の線形算術には `linarith` を使う
- `ring` は仮定を使わない。仮定を使いたい場合は `linear_combination` を検討
- `apply` が unification に失敗する場合は `refine` + `?_` で部分項を明示する
- `cases`/`induction` の前に `intro` で必要な変数を導入しておく
- 有限列挙型（`Fin n`, `Bool`, カスタム `inductive` 等）は `decide` で完全決定可能

## 関連

- **lean-simp-guide** — simp 系タクティクの詳細な使い分けガイド
- **lean-goal-advisor** サブエージェント — ゴールに対してタクティクを自動試行
- **lean-proof-planning** — 証明全体の戦略立案
