# Aesop 活用ガイド — S2IL プロジェクト向け

Aesop (Automated Extensible Search for Obvious Proofs) のプロジェクト内活用ガイド。
`@[aesop]` ルールの設計基準と、良い使い方・悪い使い方を整理する。

> **タクティク構文の詳細**: [`docs/lean/tactics/detail/自動化/aesop.md`](tactics/detail/自動化/aesop.md)  
> **Aesop 公式リポジトリ**: https://github.com/leanprover-community/aesop (Apache 2.0)

---

## 前提

- Aesop は Mathlib の推移的依存として**既に利用可能**（追加 `require` 不要）
- `import Aesop` で単体使用できる（Mathlib 経由で自動的に可用）
- **S2IL プロジェクトの REPL 環境では `import S2IL` の推移的インポート経由で Aesop が自動的に含まれる**
  - REPL デフォルト (`import S2IL + Mathlib.Tactic + Plausible + Duper`) で `aesop` タクティクが即座に使える
  - 追加の `import Aesop` は不要
- S2IL と無関係のスタンドアロン Lean ファイルでは `import Mathlib.Tactic` に Aesop は含まれないため `import Aesop` が必要

---

## Aesop とは

`aesop` タクティクは**ルールベースの自動証明探索**ライブラリ。

- `@[simp]` 補題や `@[aesop]` として登録されたルールを組み合わせ、ゴールを自動的に閉じようと試みる
- `simp` で解けない**構造的なゴール**（コンストラクタの一致・論理結合子の分解・補題の連鎖適用等）が得意
- 探索に失敗した場合はエラーになるだけで副作用はない（試して損がない）
- `aesop?` で「どのタクティクを使えば同じことができるか」の安定版スクリプトを提案してくれる
- **aesop は探索ツール**。最終証明では `aesop?` の提案に置換するのが推奨

```lean
-- 構造的なゴールを自動で閉じる
example (h : P ∧ Q) : Q ∧ P := by aesop

-- aesop? で安定版を取得
example (h : P ∧ Q) : Q ∧ P := by aesop?
-- Try this: exact ⟨h.2, h.1⟩
```

---

## Aesop の仕組み（概要）

Aesop は以下の 3 フェーズでゴールを処理する:

1. **正規化フェーズ** (`norm`): `simp_all` + ユーザー定義の正規化ルールでゴールを簡約
2. **安全ルールフェーズ** (`safe`): バックトラックなしで適用。失敗しないと信じられるルール
3. **unsafe ルールフェーズ** (`unsafe`): バックトラック付きの探索。成功確率 (%) で優先順位付け

→ 結果として `@[simp]` 補題も自動的に考慮される。

---

## 基本構文

```lean
-- 基本呼び出し
aesop

-- 安定版（証明スクリプトを提案）
aesop?

-- ルール追加（そのコールのみ有効）
aesop (add safe apply [myLemma])
aesop (add norm simp [myEq])
aesop (add unsafe 50% apply [myLemma])

-- ルール除外
aesop (erase [ruleName])

-- 探索制限の調整
aesop (config := { maxRuleApplications := 200 })
```

---

## ルール登録 (`@[aesop]` 属性)

### 3 つのフェーズ

| フェーズ | キーワード | バックトラック | 用途 |
|---|---|---|---|
| 正規化 | `norm` | なし（常に適用） | 定義展開・simp 補題・前処理 |
| 安全 | `safe` | なし（1 回のみ適用） | 確実に証明を進めるルール |
| unsafe | `unsafe N%` | あり（探索で試行） | 候補が複数ある場合の分岐 |

### 主要ビルダー

| ビルダー | 構文例 | 用途 |
|---|---|---|
| `apply` | `@[aesop safe apply]` | 補題を `apply` として登録 |
| `simp` | `@[aesop norm simp]` | simp 補題として正規化に追加 |
| `constructors` | `@[aesop safe constructors]` | 型のコンストラクタを試す |
| `cases` | `@[aesop safe cases]` | 仮定のケース分析を行う |
| `forward` | `@[aesop safe forward]` | 仮定から新しい仮定を導出 |
| `destruct` | `@[aesop norm destruct]` | forward + 元の仮定を削除 |
| `unfold` | `@[aesop norm unfold]` | 定義を 1 段展開 |
| `tactic` | `@[aesop safe tactic]` | 任意のタクティクをルール化 |

---

## 良い使い方（S2IL 推奨パターン）

### 1. `aesop` → `aesop?` → 安定版への置換

```lean
-- ✅ 開発フェーズ: aesop で閉じることを確認
example (h : P → Q) (hp : P) : Q := by aesop

-- ✅ 安定化フェーズ: aesop? で提案を得る
example (h : P → Q) (hp : P) : Q := by aesop?
-- "Try this: exact h hp"

-- ✅ 最終証明: 提案されたスクリプトに置換
example (h : P → Q) (hp : P) : Q := by exact h hp
```

> **重要**: `simp` と同様、最終証明に裸の `aesop` を残すのは非推奨。
> `aesop?` で安定版を得るか、証明が短くなる場合は直接書く。

### 2. `induction ... <;> aesop` パターン

Aesop は意図的に帰納法を自動化しない。帰納法は明示的に書き、
各ケースの閉じ込みを `aesop` に委ねるのが典型パターン。

```lean
-- ✅ 帰納法 + aesop で各ケースを閉じる
theorem append_nil {xs : MyList α} : xs ++ nil = xs := by
  induction xs <;> aesop
```

### 3. `aesop (add ...)` による局所的なルール追加

グローバルに `@[aesop]` を付けるほどではないが、特定の証明で有用な補題がある場合。

```lean
-- ✅ 局所追加（この呼び出しのみ有効）
theorem foo : ... := by
  aesop (add safe apply [helperLemma1, helperLemma2])
```

### 4. 探索用途

`simp` / `omega` / `exact?` で閉じない場合のフォールバックとして使う。

```lean
-- ✅ simp で閉じない構造的ゴール → aesop を試す
theorem bar : ... := by
  simp only [...]  -- ゴールが残った
  aesop            -- 構造的推論で閉じる
```

---

## 悪い使い方（避けるべきパターン）

### 1. 最終証明に裸の `aesop` を残す

```lean
-- ❌ Mathlib/Aesop 更新で壊れるリスク
theorem important_lemma : ... := by aesop
```

→ `aesop?` で安定版を取得するか、生成されたスクリプトに置換する。

### 2. 大規模ゴールに無条件で `aesop` を投げる

```lean
-- ❌ 探索空間が爆発して遅い（heartbeat 上限に達する）
theorem huge_lemma (s : Shape) : complexProperty s := by aesop
```

→ まず `simp` / `omega` / `cases` でゴールを分解してから試す。

### 3. `@[aesop]` の過剰な付与

```lean
-- ❌ 条件付き補題を safe に登録（ループの原因）
@[aesop safe apply]
theorem badRule (h : P) : Q ∨ R := ...

-- ❌ メタ変数を生成するルールを safe に登録
@[aesop safe apply]
theorem trans_lt : a < b → b < c → a < c := ...
```

→ メタ変数を生成するルールは `unsafe` にするか、`add` 句で局所的に追加する。

### 4. `simp` / `omega` で十分なゴールに使う

```lean
-- ❌ omega で一撃のゴールに aesop は過剰
theorem nat_ineq (n : Nat) : n + 1 > n := by aesop  -- omega で十分
```

→ 特化タクティクがある場合はそちらを優先。aesop はフォールバック。

---

## デバッグ

| 目的 | 設定 |
|---|---|
| 探索手順をトレース | `set_option trace.aesop true` |
| 探索木を表示 | `set_option trace.aesop.tree true` |
| 使用ルールセットを表示 | `set_option trace.aesop.ruleSet true` |
| パフォーマンス情報 | `set_option trace.aesop.stats true` |

---

## S2IL プロジェクトでの推奨利用方針

| 場面 | 推奨 |
|---|---|
| sorry の閉じ込み探索 | `aesop` を試す → 成功すれば `aesop?` で安定化 |
| 等変性チェーンの小補題 | `induction ... <;> aesop` パターン |
| 帰納型の全ケース消化 | `cases x <;> aesop` |
| 補題適用の自動化 | `aesop (add safe apply [...])` で局所投入 |
| 最終証明 | `aesop?` の提案に置換。裸の `aesop` は残さない |

### `@[aesop]` 属性の S2IL 設計基準

| 候補 | 登録先 | 理由 |
|---|---|---|
| `@[simp]` 付き等式 | 不要（aesop は simp_all を内蔵） | 正規化フェーズで自動利用される |
| 型のコンストラクタ | `@[aesop safe constructors]` | 存在証明・論理和の自動構築 |
| 無条件の等変性等式 | `@[aesop norm simp]` | 正規化フェーズで書き換え。`@[simp]` とは別にグローバル simp への影響なく aesop 限定で利用 |
| 条件付きの等変性定理 | `@[aesop unsafe 80% apply]` | 条件（例: `config.maxLayers ≤ 5`）はコンテキストから解決 |
| ケース分析対象型 | `@[aesop safe cases]` | 有限型の全ケース列挙 |

#### 現在 `@[aesop]` が付与されている補題一覧

**`@[aesop norm simp]`** — 無条件の等変性等式（rotate180 / rotateCW）:

| ファイル | 補題 |
|---|---|
| `QuarterPos.lean` | `isEast_rotate180`, `isWest_rotate180`, `adjacent_rotate180`, `rotateCW_rotateCW`, `adjacent_rotateCW` |
| `Rotate180Lemmas.lean` | `getDir_rotate180`, `getDir_rotateCW`, `setDir_rotate180_empty`, `setDir_rotateCW_empty`, `layers_rotate180`, `layers_rotateCW`, `getQuarter_rotate180`, `getQuarter_rotateCW`, `getQuarter_rotate180_inv`, `getQuarter_rotateCW_inv`, `setQuarter_rotate180_empty`, `setQuarter_rotateCW_empty`, `clearPositions_rotate180`, `clearPositions_rotateCW` |
| `Cutter.lean` | Layer: `eastHalf_rotate180`, `westHalf_rotate180`, `combineEastWest_rotate180`; Shape: `eastHalf_rotate180`, `westHalf_rotate180` |
| `CrystalGenerator.lean` | `fillLayer_rotate180`, `crystallize_rotate180_comm` |
| `Painter.lean` | `paintLayer_rotate180`, `paint_rotate180_comm` |
| `CrystalBond.lean` | `isBondedInLayer_rotate180`, `isBondedCrossLayer_rotate180`, `isBonded_rotate180` |
| `PinPusher.lean` | `liftUp_rotate180`, `generatePins_rotate180` |
| `Stacker.lean` | `placeAbove_rotate180`, `shatterTopCrystals_rotate180`, `truncate_rotate180` |
| `Shatter.lean` | `shatterOnCut_rotate180_comm`, `shatterOnFall_rotate180_comm`, `shatterOnTruncate_rotate180` |

**`@[aesop unsafe 80% apply]`** — 条件付きの等変性定理:

| ファイル | 補題 | 条件 |
|---|---|---|
| `PinPusher.lean` | `pinPush_rotate180_comm` | `config.maxLayers ≤ 5` |

**対象外**:
- `@[simp]` 既存の補題（aesop は `simp_all` を内蔵するため重複不要）
- `sorry` を含む定理（`stack_rotate180_comm`）
- `private` 定理

> **注意**: `@[aesop]` はグローバルに影響する。S2IL の特定モジュールでのみ使いたい場合は
> `@[local aesop]` または `@[scoped aesop]` を使い、スコープを限定する。

---

## 関連タクティクとの使い分け

| タクティク | 得意領域 | aesop との関係 |
|---|---|---|
| `simp` | 書き換え等式の連鎖 | aesop の正規化フェーズに内蔵 |
| `omega` | Nat/Int の線形算術 | aesop より高速・確実 |
| `grind` | 等式推論 + SMT | aesop と相補的。aesop が失敗→grind を試す |
| `exact?` | 単一補題の検索 | aesop より探索範囲が広いが遅い |
| `decide` | Decidable 命題 | 有限型は decide が確実 |
| `tauto` | 命題論理 | 純粋な命題論理なら tauto が軽量 |
