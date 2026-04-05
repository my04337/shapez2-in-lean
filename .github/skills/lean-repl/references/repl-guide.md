# Lean REPL エージェント向けガイド

`leanprover-community/repl` を使って Lean スニペット・タクティク・反例を即時評価する。
このガイドでは REPL・一時ファイル・Markdown の使い分け指針と、3 つのモード・pickle 戦略・ユースケース集を解説する。

## 目次

1. [REPL・一時ファイル・Markdown の使い分け](#repl一時ファイルmarkdown-の使い分け)
2. [基本的な起動方法](#基本的な起動方法)
3. [Command mode](#command-mode)
4. [Tactic mode](#tactic-mode)
5. [File mode](#file-mode)
6. [自動プレペンドによる環境初期化](#自動プレペンドによる環境初期化)
7. [エージェント向けユースケース集](#エージェント向けユースケース集)
8. [JSON 応答の読み取り方](#json-応答の読み取り方)
9. [Gotchas と制限事項](#gotchas-と制限事項)

---

## クイックリファレンス（ユースケース早見表）

このガイドで解説するユースケースの全体像。詳細は後述の各 UC セクションを参照。

| 状況・やりたいこと | 使う手法 | 対応 UC |
|---|---|---|
| `#eval` で式・値を即時確認したい | Command mode + `#eval` | [UC-1] |
| 複数の式・反例をまとめて検証したい | バッチ Command mode | [UC-2] |
| sorry のゴール状態を確認したい | sorry 投入 → `sorries[0].goal` 参照 | [UC-3] |
| 同じゴールに複数タクティクを一斉試行したい | 同一 `proofState` に複数 tactic 投入 | [UC-4] |
| 証明を段階的に組み立てたい | step-by-step tactic（分岐ごとに `proofState`） | [UC-5] |
| Mathlib 補題の型シグネチャを確認したい | `#check` | [UC-6] |
| 型クラスインスタンスの存在を確認したい | `#check (inferInstance : ...)` | [UC-7] |
| 自然言語で Mathlib 定理を探したい | `#leansearch "..."` | [UC-8] |
| 型パターンで Mathlib 定理を探したい | `#loogle "..."` | [UC-8] |
| ゴールを閉じる補題を見つけたい | tactic mode + `exact?` | [UC-8] |
| 適用可能な形の補題を探したい | tactic mode + `apply?` | [UC-8] |

---

## REPL・一時ファイル・Markdown の使い分け

証明・検証作業では 3 つのツールを目的に応じて使い分ける。

### 判断フロー

```
検証したいコードがある
  ├─ 数行・定義不要・即時確認  →  REPL（~11-20s 初回起動、以降はキャッシュで短縮）
  ├─ 複数定義が必要・10行以上  →  Scratch/*.lean
  └─ 証明骨格・仮説・自然言語メモ  →  Markdown（session memory / docs/）
```

### ツールごとの指針

| ツール | 向いている場面 | 向いていない場面 |
|---|---|---|
| **REPL** | 単発 `#eval`・tactic 探索・sorry ゴール・バッチ反例 | 複雑なインポート構成・長大なコードブロック |
| **`Scratch/*.lean`** | 複数定義が必要・10行以上・ファイルとして保存したい | トップレベルへの作成・恒久的なコードの保管 |
| **Markdown** | 証明骨格メモ・仮説の記録・次セッションへの申し送り | コードの実行・構文チェック |

### `Scratch/` ディレクトリのルール

一時的な `.lean` ファイルはプロジェクトルートの **`Scratch/`** ディレクトリに作成する。

```
Scratch/
  GravityCheck.lean    ← 内容を反映した UpperCamelCase のファイル名
  CutterCommute.lean
```

- **ファイル名**: `UpperCamelCase`、内容を端的に表す名前
- **型チェックのみ（`#eval` 有効）**: `lake env lean Scratch/MyFile.lean`（`lakefile.toml` への登録不要）
- **`def main` を実行**: `lake env lean --run Scratch/MyFile.lean`（`--run` は**ファイル名より前**に置く）
- **REPL file mode**: `{"path": "Scratch/MyFile.lean", "allTactics": true}`
- **`lake build` の対象外**: `defaultTargets` に含まれないためメインビルドに影響しない
- **トップレベルへの作成禁止**: `check_*.lean`・`tmp_*.lean` 等をトップレベルに作らない

> **Markdown メモの保存先**:
> - 単一セッションのメモ → `/memories/session/`
> - 複数セッションにまたがる知見 → `/memories/repo/` または `docs/knowledge/`

### NG パターン

```
❌ ./check_foo.lean       ← トップレベルへの一時ファイル作成
❌ ./tmp_test.lean        ← 同上
✅ Scratch/FooCheck.lean  ← Scratch/ 以下に作成
✅ REPL の #eval          ← 数行の即時確認はファイル不要
```

---

## 基本的な起動方法

### スクリプト経由（推奨）

```powershell
# Windows — JSONL ファイルを渡して実行
# ⚠️ .jsonl ファイルは必ず Scratch/ ディレクトリに配置すること（.gitignore 管理）
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands.jsonl

# Windows — pickle を強制再生成
.github/skills/lean-repl/scripts/repl.ps1 -RebuildPickle

# macOS / Linux
.github/skills/lean-repl/scripts/repl.sh --input Scratch/commands.jsonl
.github/skills/lean-repl/scripts/repl.sh --rebuild-pickle
```

### lake exe repl を直接使う場合

```powershell
# 単発コマンド（S2IL なし）
'{"cmd": "#eval 1 + 1"}' | lake exe repl

# ファイルから読み込む
Get-Content Scratch/commands.jsonl | lake exe repl
```

---

## Command mode

最も基本的なモード。Lean の宣言・式を評価し、環境 ID を返す。

### プロトコル

```
入力: {"cmd": "<Lean コード>"}           # 新規環境
入力: {"cmd": "<Lean コード>", "env": N} # 環境 N を継続
```

### env の継続と分岐

```jsonl
{"cmd": "def x := 1"}

{"cmd": "#eval x + 1", "env": 0}

{"cmd": "def x := 100", "env": 0}

{"cmd": "#eval x", "env": 2}
```

`env` 値を使い回すことでバックトラック（分岐探索）ができる。

### import の制約

`import` は **`env` フィールドなしのコマンドでのみ**使用可能。
S2IL をインポートした環境は pickle にキャッシュして再利用する（後述）。

---

## Tactic mode

sorry を含むコマンドを投入して `proofState` を取得し、タクティクを 1 ステップずつ試す。

### プロトコル

```
step 1: {"cmd": "... := by sorry"} → {"sorries": [{"proofState": N, "goal": "..."}]}
step 2: {"tactic": "<tactic>", "proofState": N} → {"proofState": M, "goals": [...]}
```

### 使用例

```jsonl
{"cmd": "import S2IL\nopen S2IL\ntheorem foo (n : Nat) : n + 0 = n := by sorry"}

{"tactic": "simp", "proofState": 0}

{"tactic": "omega", "proofState": 0}

{"tactic": "rfl", "proofState": 0}
```

- 同一 `proofState` に対して複数タクティクを並列に試せる（REPL が状態を保持）
- `goals: []` が返れば証明完了
- `goals` にまだゴールが残っていれば次のタクティクが必要

### sorry を含む tactic

tactic 内で `sorry` を使うと追加の `proofState` が返る（サブゴールの探索に使える）。

---

## File mode

ファイル全体を評価し、含まれるタクティクの一覧と実行結果を取得する。

```jsonl
{"path": "Scratch/MyFile.lean", "allTactics": true}
```

```json
{
  "tactics": [
    {"tactic": "exact rfl", "proofState": 0, "goals": "⊢ f + g = 39", ...}
  ],
  "env": 0
}
```

---

## 自動プレペンドによる環境初期化

REPL スクリプトはデフォルトで `import S2IL\nimport Mathlib.Tactic` を先頭コマンドとして自動追加する。
この自動プレペンドにより `env: 0` には S2IL + Mathlib.Tactic が利用可能な環境が作られる。
`ring` / `linarith` / `exact?` / `#leansearch` / `#loogle` など全ての Mathlib タクティクが使える。

### 起動時間

初回は `import` が走るため `~11–20s` かかる。2 回目以降は Lean が `.olean` キャッシュを使用するため速くなる。

### `-NoPickle` フラグ（上級者向け）

自動プレペンドを抑制し、JSONL 内でインポートを完全に自己管理したい場合に使う。

```powershell
# 自動プレペンドなし（JSONL 内に import 文を書く）
.github/skills/lean-repl/scripts/repl.ps1 -NoPickle -InputFile Scratch/commands.jsonl
```

### pickle（.olean キャッシュ）について

```powershell
# pickle を再生成する（S2IL ソース変更後）
.github/skills/lean-repl/scripts/repl.ps1 -RebuildPickle
```

pickle ファイルは `.repl/s2il.olean` に保存される。ただし pickle を使っても環境初期化には
`import` の実行が必要なため、起動時間の短縮効果は限定的（内部的には自動プレペンドと同等）。

---

## エージェント向けユースケース集

### [UC-1] 単発 `#eval` による高速反例チェック

```jsonl
{"cmd": "#eval toString Color.red", "env": 0}
```

上記を `Scratch/commands.jsonl` に保存して:
```powershell
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands.jsonl
```

### [UC-2] バッチ反例チェック（N ケース）

1 セッション内で連続送信することで最大効果を得られる。

```jsonl
{"cmd": "#eval ([Color.red, Color.green, Color.blue] : List Color).map toString", "env": 0}

{"cmd": "#eval decide (∀ d : Direction, d = d)", "env": 0}
```

### [UC-3] sorry のゴール確認と原因分析

```jsonl
{"cmd": "theorem myGoal (s : Shape) (h : s.layers.length > 0) : s.layers.length ≤ 4 := by\n  sorry", "env": 0}
```

応答の `sorries[0].goal` に現在のゴール状態が入る。

### [UC-4] タクティク探索（同一ゴールに複数候補）

```jsonl
{"cmd": "theorem test (n : Nat) : n + 0 = n := by sorry", "env": 0}

{"tactic": "simp", "proofState": 0}

{"tactic": "omega", "proofState": 0}

{"tactic": "rfl", "proofState": 0}

{"tactic": "exact Nat.add_zero n", "proofState": 0}
```

### [UC-5] 証明骨格の段階的構築

```jsonl
{"cmd": "theorem step1 ... := by\n  intro h\n  sorry", "env": 0}

{"tactic": "cases h with\n  | inl h1 => sorry\n  | inr h2 => sorry", "proofState": 0}
```

分岐の各 `sorry` に新しい `proofState` が返る。各ブランチを独立して攻略できる。

### [UC-6] Mathlib の補題確認

```jsonl
{"cmd": "#check Nat.add_comm", "env": 0}

{"cmd": "#check List.length_map", "env": 0}
```

### [UC-7] 型クラスインスタンスの存在確認

```jsonl
{"cmd": "#check (inferInstance : BEq Direction)", "env": 0}

{"cmd": "#check (inferInstance : DecidableEq Color)", "env": 0}
```

### [UC-8] Mathlib 定理の検索

証明中に使えそうな Mathlib 補題を調べる方法は 3 つある。用途に応じて使い分ける。

#### 自然言語検索（`#leansearch`）

ゴール状態や証明したい性質を自然言語で記述して検索する。英語クエリを推奨。

> クエリ文字列は末尾を `.` または `?` で終わらせること。

```jsonl
{"cmd": "#leansearch \"list permutation preserves foldl with commutative function.\"", "env": 0}

{"cmd": "#leansearch \"if perm and nodup then foldl equal.\"", "env": 0}
```

実行方法:
```powershell
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands.jsonl
```

#### 型パターン検索（`#loogle`）

型シグネチャのパターンで検索する。具体的な型が分かっているときに有効。

```jsonl
{"cmd": "#loogle \"List.Perm\"", "env": 0}

{"cmd": "#loogle \"List.Nodup → List.Perm\"", "env": 0}

{"cmd": "#loogle \"|- List.foldl _ _ _ = List.foldl _ _ _\"", "env": 0}
```

#### 候補を絞り込んでから `#check`

検索結果の候補名を `#check` で型シグネチャを確認してから使う。

> ⚠️ 存在しない宣言名や複雑な型クラス制約を持つ宣言を `#check` するとREPL がクラッシュする。補題検索で得た名前のみを渡すこと。

```jsonl
{"cmd": "#check List.Perm.length_eq", "env": 0}

{"cmd": "#check Nat.lt_of_succ_le", "env": 0}
```

#### `exact?` / `apply?` でゴール直結検索

ソースファイルの sorry 位置で既にゴールが分かっている場合は tactic mode で直接試す。

```jsonl
{"cmd": "-- ゴールが List.Perm l1 l2 → ... の形の場合\ntheorem search_test (l1 l2 : List Nat) (h : l1.Perm l2) : l1.length = l2.length := by sorry", "env": 0}

{"tactic": "exact?", "proofState": 0}

{"tactic": "apply?", "proofState": 0}
```

#### 使い分け早見表

| 状況 | 使うコマンド |
|---|---|
| 何が使えるか分からない・ゴールを言葉で説明できる | `#leansearch` |
| 型の形は分かっている・具体的な演算子が含まれる | `#loogle` |
| 候補名が分かった・型シグネチャを確認したい | `#check` |
| ゴール状態がある・完全一致を探したい | tactic mode + `exact?` |
| 適用できる形の補題を探したい | tactic mode + `apply?` |

---

## JSON 応答の読み取り方

### スクリプト出力仕様（`-InputFile` / `--input` モード）

- **stdout**: 各 REPL 応答が **1 行 JSON** として出力される（複数行プリティプリントは自動圧縮）
- **stderr**: ビルドメッセージ・ステータスメッセージ（JSON ではない）
- **終了コード**: `0`=正常, `1`=REPL 応答にエラーあり, `2`=REPL クラッシュ
- クラッシュ時は最終行に `{"error":"repl_crashed","message":"...","commands_sent":N,"responses_received":M}` が出力される

### Command mode 応答

```json
{"env":2,"messages":[{"severity":"info","pos":{"line":1,"column":0},"endPos":{"line":1,"column":5},"data":"14"}]}
```

| フィールド | 説明 |
|---|---|
| `env` | 次回使用可能な環境 ID |
| `messages[].severity` | `info` / `warning` / `error` |
| `messages[].data` | `#eval` の出力やエラー文字列 |
| `sorries[].goal` | sorry 箇所のゴール文字列 |
| `sorries[].proofState` | tactic mode で使う証明状態 ID |

### Tactic mode 応答

```json
{"proofState":1,"goals":["n : Nat\n⊢ n = n"]}
```

`goals: []` → 証明完了。

### unpickle 応答

```json
{"env":0}
```

`env: 0` が S2IL 読み込み済み環境。以降のコマンドには `"env": 0` を指定する。

デフォルトモードでは自動プレペンドで `env: 0` が作成されるため、JSONL 内で `unpickleEnvFrom` を書く必要はない。

---

## Gotchas と制限事項

| 問題 | 対策 |
|---|---|
| **コマンド間の区切りが空行でない** | 各コマンドの間には必ず 1 行の**空行**を入れる。空行がないと REPL が複数コマンドを 1 つの JSON として解釈しパースエラーになる（例: `Could not parse JSON`） |
| `import` コマンドを `env` 指定と同時に使うとエラー | `import` は `env` なしコマンドのみ使用可。デフォルトモードでは自動プレペンドが `env: 0` を作るので JSONL に `import` を書く必要はない |
| pickle が無効（S2IL 変更後） | `-RebuildPickle` で再生成（スクリプトが起動失敗を検知して自動再生成も行う） |
| tactic mode の完了 proof state は現状 env に反映できない | tactic が成功しても `env` は更新されない。完全な証明は元ファイルに書く |
| scoped notation を pickle に含めると正しく復元されない場合がある | scoped 宣言は pickle 後のセッションで改めて定義する |
| REPL は stdin 読み込みが終わるまで応答しない場合がある | JSONL ファイルを `-InputFile` で渡す方が安定 |
| `sorry` を含む定理の `#eval` 結果は信頼できない | 反例チェックは sorry のない状態で行う |
| **`open S2IL in` が "unknown namespace" エラーになる** | `S2IL` はモジュール名であり Lean 名前空間ではない。`import S2IL` 後は `Color`, `Direction`, `GameConfig` 等がグローバルに参照可能。個別名前空間を開くには `open Color in` を使う |
| **【PowerShell】`-Input` 代わりに `-InputFile` を使う** | `-Input` は PowerShell の `$input` 自動変数（パイプライン列挙子）と衝突する。スクリプトパラメータは `-InputFile` |
| **【PowerShell】`pickleTo` 応答に `messages` フィールドがなく StrictMode 例外が発生する** | 応答 JSON と `$obj.messages` 等を参照する前に `$obj.PSObject.Properties['messages']` で存在確認する。`Set-StrictMode -Version Latest` 環境では必須 |
| **`#check` に存在しない宣言名を渡すと REPL がクラッシュ** | 補題検索（`exact?` / `#leansearch` 等）で確認した名前のみ `#check` に渡す |
