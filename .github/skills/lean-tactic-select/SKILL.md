---
name: lean-tactic-select
description: >
  Goal-shape → prioritized tactic mapping (equality / arith / ∀ / ∃ / ∧ / ∨ / inductive / decidable / contradiction).
  Use when: which tactic, tactic selection, goal analysis, what tactic to use, stuck on goal,
  tactic advice, next tactic, tactic recommendation, goal shape, choose tactic,
  どのタクティク, タクティク選択, ゴール分類.
  Returns: priority map keyed by goal shape + tie-breaking heuristics.
  Don't call when: you want the agent to actually try the tactics (use agent `lean-sorry-investigator`).
metadata:
  argument-hint: 'Reference: goal shape → tactic priority map'
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
2. aesop    — ルールベース自動証明（@[simp] + @[aesop] ルールで探索）
3. duper [*] — 超位置推論ベースの一階述語論理自動証明。仮定からの論理推論チェーンに強い
4. grind    — SMT 風自動証明（等式推論 + 線形算術 + ケース分割）
5. simp_all — 全仮定+ゴールを一括簡約
6. sorry    — 一時スキップして骨格を確立
```

**`aesop` の使い方**:
- `aesop` は `simp_all` を内蔵した正規化 + ルールベース探索。`simp` で閉じない構造的ゴールに有効
- S2IL では rotate180/rotateCW 等変性の基本等式 37 件が `@[aesop norm simp]` で登録済み。等変性ゴールは `aesop` で自動閉じ込みできる場合が多い
- 成功したら `aesop?` でスクリプトを取得し、最終証明では安定版に置換する
- `induction x <;> aesop` / `cases x <;> aesop` で帰納型の各ケースを自動閉じ込みできる
- 局所的に補題を追加: `aesop (add safe apply [lemma1, lemma2])`
- 詳細: [`docs/lean/aesop-guide.md`](../../../docs/lean/aesop-guide.md)

**`duper` の使い方**:
- `duper [*]` でローカルコンテキストの全仮定を渡す。成功したら `duper?` で `portfolioInstance` を取得し安定化
- `duper [h1, h2, lemma_name]` で必要な仮定・外部補題だけを選別して渡すことも可能
- 一階述語論理の推論チェーン（`∀`, `∃`, `→`, `∧`, `∨`）に強い
- **帰納法・高階関数・算術ゴールには向かない**（`induction` / `omega` を先に使う）
- 詳細: [`docs/lean/duper-guide.md`](../../../docs/lean/duper-guide.md)

> **補題名が不明な場合**: `exact?` で見つからなければ **lean-mathlib-search** スキル（または **lean-sorry-investigator** エージェント）で `#leansearch` / `#loogle` を含む段階的検索を実行する。

---

## Step 4: REPL でのタクティク試行

REPL スクリプトが `import S2IL + Mathlib.Tactic + Plausible + Duper` を先頭に自動挿入するため、JSONL 内では `"env": 0` を直接使える。
ring, linarith, nlinarith, exact?, funext, simp?, aesop, plausible, duper 等すべての Mathlib タクティクと外部タクティクが利用可能。

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
- `aesop` も探索用。最終証明では `aesop?` でスクリプトを取得し置換する。裸の `aesop` は非推奨
- `duper` も探索用。最終証明では `duper?` で `portfolioInstance` を取得し置換する。裸の `duper [*]` は非推奨
- `plausible` は証明ではない。「反例なし」は「真っぽい」の確認のみ。最終証明に使用禁止
- `omega` は Nat/Int 専用。ℝ/ℚ の線形算術には `linarith` を使う
- `ring` は仮定を使わない。仮定を使いたい場合は `linear_combination` を検討
- `apply` が unification に失敗する場合は `refine` + `?_` で部分項を明示する
- `cases`/`induction` の前に `intro` で必要な変数を導入しておく
- 有限列挙型（`Fin n`, `Bool`, カスタム `inductive` 等）は `decide` で完全決定可能

## 関連

- **lean-simp-guide** — simp 系タクティクの詳細な使い分けガイド
- **[Aesop 活用ガイド](../../../docs/lean/aesop-guide.md)** — aesop のルール設計基準・良い/悪い使い方
- **[Duper 活用ガイド](../../../docs/lean/duper-guide.md)** — duper (超位置推論 ATP) の良い/悪い使い方・デバッグ方法
- **[Plausible 活用ガイド](../../../docs/lean/plausible-guide.md)** — plausible タクティクの良い/悪い使い方・S2IL での適用範囲
- **lean-sorry-investigator** エージェント — 1 件の sorry に対してタクティクを自動試行し要約を返す
- **lean-proof-planning** — 証明全体の戦略立案
