# Lean 4 命名規則リファレンス

> **位置づけ**: このドキュメントは Lean 4 / Mathlib の一般的な命名規則をまとめたリファレンスです。
> S2IL プロジェクト固有のスタイルルールは [`S2IL/AGENTS.md`](../../S2IL/AGENTS.md) の「Lean 4 命名規則」セクションを参照してください。
>
> 参考:
> - [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
> - [Library style guidelines](https://leanprover-community.github.io/contribute/style.html)

---

## 基本ルール（大文字・小文字の使い分け）

命名規則は**宣言の返り値の型**で決まる。

| 分類 | ケース | 対象 | 例 |
|---|---|---|---|
| `Prop` の項（証明） | `snake_case` | 定理・補題・証明 | `add_comm`, `zero_add`, `succ_ne_zero`, `mul_pos` |
| `Prop` / `Type` / `Sort` 自体 | `UpperCamelCase` | 帰納型・構造体・クラス | `Nat`, `List`, `OneHom`, `HPow` |
| 上記以外の `Type` の項 | `lowerCamelCase` | 関数・定義・値 | `toString`, `getSize`, `List.map` |

関数は**返り値の型**に従って命名する:
- `A → B → Prop` を返す関数（定理として使える） → `snake_case`（例: `lt_of_succ_le`）
- `A → Type` を返す関数（型構築） → `UpperCamelCase`（例: `CategoryTheory.Functor`）
- `A → B` で `B` が `Type` の項 → `lowerCamelCase`（例: `List.length`, `toString`）

## 名前空間・ファイル名

- 名前空間: `UpperCamelCase`（例: `Nat`, `List`, `S2IL`）
- `.lean` ファイル名: `UpperCamelCase`（例: `Basic.lean`, `NatColor.lean`）

## 略語（アクロニム）の扱い

略語はケースに応じてグループ単位で大文字・小文字にする。単語の途中で大文字小文字を混ぜない。

| ケース | 例 |
|---|---|
| `UpperCamelCase` 中 | `HPow`, `LT`, `LE`, `IO` |
| `lowerCamelCase` 中 | `hPow`, `lt`, `le`, `io` |
| `snake_case` 中 | `h_pow`, `lt_iff_le`, `io_bind` |

## 構造体フィールド・コンストラクタ

フィールドやコンストラクタも基本ルールに従う。

```lean
structure OneHom (M : Type) (N : Type) [One M] [One N] where
    toFun : M → N                -- lowerCamelCase（Type の項）
    map_one' : toFun 1 = 1       -- snake_case（Prop の項 = 証明義務）
```

**証明フィールド**（構造体の不変条件）は、フィールド名 + `_` + 性質の簡潔な記述子で命名する。

| パターン | 例 | 意味 |
|---|---|---|
| フィールド名 + `_ne` | `layers_ne` | `layers ≠ []`（空でない） |
| フィールド名 + `_pos` | `maxLayers_pos` | `0 < maxLayers`（正） |
| フィールド名 + `_lt` | `index_lt` | `index < bound`（上界未満） |

## ドット記法と名前空間

- 型名を名前空間として関数を定義し、ドット記法で呼び出す
  ```lean
  def List.map (f : α → β) : List α → List β := ...
  #eval [1, 2, 3].map (· + 1)
  ```
- 論理結合子のイントロ・エリム等もドット記法を活用する
  - `And.intro`, `And.left`, `Or.inl`, `Eq.symm`, `Eq.trans` など

## Prop-valued クラス（述語クラス）の命名

- 名詞の場合: `Is` 接頭辞を付ける（例: `IsTopologicalRing`, `IsEmpty`）
- 形容詞の場合: `Is` 接頭辞は不要（例: `Normal`, `Finite`）
- 述語関数: `is` / `has` 接頭辞を使用（例: `isEven`, `hasDecEq`）

## 定理名の説明的命名パターン

定理名は基本的に**結論を描写**する。仮定の記述が必要な場合は `_of_` で区切る。

| パターン | 例 | 意味 |
|---|---|---|
| 結論をそのまま | `mul_zero`, `succ_ne_zero` | `a * 0 = 0`, `succ n ≠ 0` |
| `_of_` で仮定記述 | `lt_of_succ_le`, `lt_of_le_of_ne` | 仮定の順に列挙 |

---

## 新規補題の命名フロー（エージェント運用ルール）

新規補題を導入するときは、以下の 3 段階で名前を確定し、**仮称をドキュメントに残さない**。
これは sorry-plan.json / sorry-card / symbol-map.jsonl の整合性を保ち、補題検索のヒット率を高めるための必須ルール。

### ステップ 1: REPL で仮称シグネチャをスケッチ

```lean
example (s : Shape) ... : ... := by sorry
```

- 名前は `example` のままでよい（この時点では確定しない）
- 型だけ REPL で通すことが目的

### ステップ 2: REPL 型チェック通過後に確定名を決める

確定名は以下を満たすまで確定しない:

1. 本ファイルの基本ルール（返り値の型別 case、`_of_` 区切り）に従っている
2. 既存の類似補題（symbol-map.jsonl で `grep` して確認）と命名パターンが揃っている
3. 対象となる操作の層（Shape / Layer / Gravity / …）を接頭辞に含める

### ステップ 3: 確定名をまず `sorry-plan.json` に記録

- 新補題の **確定名** を `ready_lemmas` または `remaining_steps.title` に登録する
- sorry-card にも記入する場合は **確定名のみ** を書く
- **仮称（`_persists_`, `_tmp_` など）を sorry-card / 本文コメントに残さない**
- 確定名を途中で変更した場合は、以下を同時に grep して全箇所を更新:
  - `S2IL/**/*.lean`
  - `S2IL/_agent/sorry-plan.json`
  - `S2IL/_agent/sorry-cards/*.md`
  - `docs/plans/*.md`

### 違反例（過去の実績）

- 2026-04-22 Step 0.2 で sorry-card に `placeLDGroups_landing_persists_nonEmpty`（仮称）と `placeLDGroups_landing_nonEmpty`（確定名）が混在。
  - 原因: REPL 確定前に sorry-card を先に書いた → 書き直し忘れ
  - 対策: 本フローを `AGENTS.md` 証明作業セクションにも明示

### 関連

- 詳細な運用は [`docs/agent/proof-plan-current-focus-guide.md`](../agent/proof-plan-current-focus-guide.md) の「役割分担」セクションを参照
- 確定名の検索: [`S2IL/_agent/symbol-map.jsonl`](../../S2IL/_agent/symbol-map.jsonl) を `grep_search` で検索
| `_left` / `_right` | `add_le_add_left` | 左右の変形 |
| 省略形 | `pos`, `neg`, `nonpos`, `nonneg` | `0 < x`, `x < 0`, `x ≤ 0`, `0 ≤ x` |
| 公理的性質 | `refl`, `symm`, `trans`, `comm`, `assoc` | 反射・対称・推移・交換・結合 |

## `UpperCamelCase` を `snake_case` 中で参照する場合

`UpperCamelCase` の名前が `snake_case` の定理名中に現れるときは `lowerCamelCase` に変換する。

```lean
-- MonoidHom → monoidHom, OneHom → oneHom
theorem MonoidHom.toOneHom_injective : ...
-- Nat.cast → natCast
theorem map_natCast : ...
```

## 変数名の慣例（Lean / Mathlib 標準）

| 変数 | 用途 |
|---|---|
| `u`, `v`, `w` | 宇宙レベル |
| `α`, `β`, `γ` | 汎用的な型 |
| `x`, `y`, `z` | 汎用型の要素 |
| `h`, `h₁`, `h₂` | 仮定・仮説 |
| `p`, `q`, `r` | 述語・関係 |
| `m`, `n`, `k` | 自然数 |
| `i`, `j`, `k` | 整数 |
| `s`, `t` | リスト・集合 |
| `f`, `g` | 関数 |
