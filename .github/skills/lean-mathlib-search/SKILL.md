---
name: lean-mathlib-search
description: >
  Search Mathlib/Batteries for lemmas that close a Lean 4 proof goal.
  Use when: find lemma, search mathlib, exact?, apply?, loogle, leansearch,
  which lemma, lemma search, mathlib lookup, batteries lemma,
  List lemma, unknown lemma name, find matching theorem,
  補題を探す, what lemma to use, lemma for goal,
  補題名が分からない, どの補題を使う, Mathlib 検索, Batteries 補題,
  補題探索, 補題が見つからない, どの定理を使う, 補題がない.
metadata:
  argument-hint: 'Pass goal state or describe the goal'
---

# Mathlib / Batteries 補題検索スキル

ゴールを閉じる補題の名前が分からないとき、4 つの検索ツールを段階的に使って補題を発見する。

> 詳細なリファレンス: [`references/mathlib-search-guide.md`](references/mathlib-search-guide.md)

---

## クイック判断: 検索が必要か？

| 状況 | アクション |
|---|---|
| ゴールが `a < b` / `a = b`（Nat/Int 線形） | まず `omega` / `norm_num` を試す。補題検索は不要かも |
| ゴールが有限型の全探索可能 | `decide` を試す |
| S2IL 補題で閉じそう / `@[simp]` 補題で閉じそう | `simp?` → 使われた補題名を確認 |
| ゴールに `↑`（キャスト）が含まれる | `norm_cast` で正規化してから再試行 |
| 上記で解決しない / 汎用ライブラリ補題が欲しい | **このスキルの手順に進む** |

---

## Step 1: ゴール形状の分類と検索戦略の選択

ゴールの型を確認し、最適な検索ツールを選ぶ。

| ゴール形状 | 第1候補 | 第2候補 | 補足 |
|---|---|---|---|
| 具体的な型を含む等式 (`List.map`, `Option.bind` 等) | `exact?` | `#loogle` | 型パターンが明確 |
| 具体的な型を含む不等式・関係 | `apply?` | `#loogle` | 前提の引数が残ることが多い |
| 概念的に何が欲しいか説明できる | `#leansearch` | `#loogle` | 自然言語で試す |
| S2IL ドメイン型のゴール | `exact?` / `simp?` | — | Mathlib に対応なし |

---

## Step 2: REPL 検索の実行

REPL スクリプトが `import S2IL + Mathlib.Tactic + Plausible + Duper` を先頭に自動挿入するため、JSONL 内では `"env": 0` を直接使える。
`exact?` / `apply?` / `#leansearch` / `#loogle` すべてがデフォルトモードで動作する。

### 2a: `exact?` / `apply?`

sorry のゴールを REPL で取得し、直接 `exact?` / `apply?` を試す。

```jsonl
{"cmd": "<sorry を含む定理コード>", "env": 0}

{"tactic": "exact?", "proofState": 0}

{"tactic": "apply?", "proofState": 0}
```

```powershell
# Windows — Persistent モード（推奨・~600ms/回）
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/lemma_search.jsonl

# Windows — バッチモード（レガシー・Persistent が利用できない場合のみ）
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/lemma_search.jsonl
```

```bash
# macOS / Linux — Persistent モード（推奨・~600ms/回。bash 4+ 必須）
.github/skills/lean-repl/scripts/repl.sh --send --session-id <id> --cmd-file Scratch/lemma_search.jsonl

# macOS / Linux — バッチモード（レガシー）
.github/skills/lean-repl/scripts/repl.sh --input Scratch/lemma_search.jsonl
```

**結果の読み方**:
- `goals: []` + `messages` に `Try this: exact <lemma>` → **成功**。その補題を使う
- `messages` に `Try this: apply <lemma>` → **部分成功**。残ゴールとセットで報告
- エラー / タイムアウト → Step 2b へ

### 2b: `#leansearch` / `#loogle`

`exact?` / `apply?` で見つからない場合、自然言語・型パターンで広く検索する。

```jsonl
{"cmd": "#leansearch \"<ゴールを英語で説明>.\"", "env": 0}

{"cmd": "#loogle \"<型パターン>\"", "env": 0}
```

```powershell
# Windows — Persistent モード（推奨・~600ms/回）
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/lemma_search.jsonl

# Windows — バッチモード（レガシー・Persistent が利用できない場合のみ）
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/lemma_search.jsonl
```

```bash
# macOS / Linux — Persistent モード（推奨・~600ms/回。bash 4+ 必須）
.github/skills/lean-repl/scripts/repl.sh --send --session-id <id> --cmd-file Scratch/lemma_search.jsonl

# macOS / Linux — バッチモード（レガシー）
.github/skills/lean-repl/scripts/repl.sh --input Scratch/lemma_search.jsonl
```

**`#leansearch` クエリの作り方**:
- ゴール `l.map f |>.filter p = (l.filter (p ∘ f)).map f` → `"filter of mapped list equals map of filtered list."`
- ゴール `l1.Perm l2 → l1.length = l2.length` → `"permutation preserves length."`
- 末尾は `.` または `?` で終わらせる（必須）

**`#loogle` クエリの作り方（REPL では定数名直接指定が有効）**:
- ゴール `(l.map f).length = l.length` → `#loogle "List.length_map"`（名前規則から推測）
- ゴール `(l.filter p).length ≤ l.length` → `#loogle "List.length_filter_le"`
- 上記で見つからない場合 → `#leansearch "length of filtered list is at most original length."`

---

## Step 3: 候補の検証

検索で得られた候補を実際にゴールに適用して確認する。

```jsonl
{"cmd": "#check @<候補補題名>", "env": 0}

{"cmd": "<sorry を含む定理コード>", "env": 0}

{"tactic": "exact <候補補題名> <引数>", "proofState": 0}
```

**確認ポイント**:
- 型シグネチャの前提条件（型クラス制約 `[LawfulBEq]` 等）が満たせるか
- 暗黙引数の推論が通るか
- `exact` で直接適用できなければ `rw [<補題>]` → サブゴール確認

---

## Step 4: 結果の報告とナレッジ更新

### 報告フォーマット

**検索結果**: `<ゴール概要>`

| # | 補題名 | 適用方法 | 結果 |
|---|---|---|---|
| 1 | `List.map_map` | `exact List.map_map g f l` | ✅ 完全解決 |
| 2 | `List.filter_map` | `rw [List.filter_map]` | ⚡ サブゴール残 |

**推奨**: `<補題名>` を `<タクティク>` で使う。

### ナレッジ更新の提案

初めて発見した有用な Batteries/Mathlib 補題は [`references/batteries-catalog.md`](references/batteries-catalog.md) への追記を提案する:
- 補題名・シグネチャ・前提条件・使用例

ただし追記は報告のみ。実際の編集はユーザー判断に委ねる。

---

## Gotchas

- `#loogle` の `_` プレースホルダー付きパターン（`List.filter _ _` 等）は REPL では結果が返らないことが多い。**定数名を直接指定する**（例: `#loogle "List.length_filter_le"`）か `#leansearch` を使う
- `#leansearch` のクエリは**英語**で書く。末尾に `.` または `?` を忘れると結果が返らない
- S2IL ドメイン型（`Shape`, `Layer` 等）は Mathlib に存在しないため、`#leansearch` / `#loogle` では見つからない。`exact?` / `simp?` を使う
- 存在しない宣言名を `#check` するとエラー応答（`Unknown identifier`）が返る。REPL はクラッシュしないが、exit code は 1 になる
- `BEq.comm` は `LawfulBEq` インスタンスが必要。`deriving DecidableEq, BEq` の型なら自動的に持つ

---

## 関連

- **エージェント**: `lean-lemma-finder`（本スキルの手順を自動実行するサブエージェント）
- **スキル**: `lean-tactic-select`（タクティク選択。補題検索の前にまず試すべき戦略を判断）
- **スキル**: `lean-repl`（REPL の詳細な使い方。UC-8 が補題検索）
- **リファレンス**: [`references/mathlib-search-guide.md`](references/mathlib-search-guide.md)
- **補題カタログ**: [`references/batteries-catalog.md`](references/batteries-catalog.md)（発見済み補題・置換パターン）
- **関連ドキュメント**: [`docs/lean/README.md`](../../../docs/lean/README.md)（Lean 関連ガイドの入口）
