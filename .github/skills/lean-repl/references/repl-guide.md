# Lean REPL エージェント向けガイド

`leanprover-community/repl` を使って Lean スニペット・タクティク・反例を即時評価する。
このガイドでは REPL・一時ファイル・Markdown の使い分け指針と、3 つのモード・pickle 戦略・ユースケース集を解説する。

## 目次

1. [REPL・一時ファイル・Markdown の使い分け](#repl一時ファイルmarkdown-の使い分け)
2. [基本的な起動方法](#基本的な起動方法)
3. [Command mode](#command-mode)
4. [Tactic mode](#tactic-mode)
5. [File mode](#file-mode)
6. [自動先頭挿入による環境初期化](#自動先頭挿入による環境初期化)
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
> - 複数セッションにまたがる知見 → `/memories/repo/` または `docs/s2il/`（S2IL 固有）/ `docs/lean/`（Lean 一般）

### NG パターン

```
❌ ./check_foo.lean       ← トップレベルへの一時ファイル作成
❌ ./tmp_test.lean        ← 同上
✅ Scratch/FooCheck.lean  ← Scratch/ 以下に作成
✅ REPL の #eval          ← 数行の即時確認はファイル不要
```

---

## 基本的な起動方法

### Persistent モード経由（推奨・~600ms/回）

```powershell
# Windows — Persistent モードでコマンド送信（初回のみ ~13s、以降 ~600ms）
# ⚠️ .jsonl ファイルは必ず Scratch/ ディレクトリに配置すること（.gitignore 管理）
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands-<sessionId>-<topic>-<runId>.jsonl
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -Cmd '{"cmd": "#eval 1 + 1"}'
```

```bash
# macOS / Linux — Persistent モードでコマンド送信（初回のみ ~13s、以降 ~600ms）
# ⚠️ .jsonl ファイルは必ず Scratch/ ディレクトリに配置すること（.gitignore 管理）
# ⚠️ bash 4+ が必要（macOS のデフォルト bash 3.x では動作しない。brew install bash 等で対応）
.github/skills/lean-repl/scripts/repl.sh --send --session-id <id> --cmd-file Scratch/commands-<sessionId>-<topic>-<runId>.jsonl
.github/skills/lean-repl/scripts/repl.sh --send --session-id <id> --cmd '{"cmd": "#eval 1 + 1"}'
```

#### Persistent セッション管理

```powershell
# Windows — セッション開始（import 完了まで待機、初回 ~13s）
.github/skills/lean-repl/scripts/repl.ps1 -Start -SessionId <id>
# Windows — セッション停止
.github/skills/lean-repl/scripts/repl.ps1 -Stop -SessionId <id>
```

```bash
# macOS / Linux — セッション開始（import 完了まで待機、初回 ~13s）
.github/skills/lean-repl/scripts/repl.sh --start --session-id <id>
# macOS / Linux — セッション停止
.github/skills/lean-repl/scripts/repl.sh --stop --session-id <id>
```

- **Lazy Start**: `--send` / `-Send` 時にデーモンが起動していなければ自動起動する。明示的な `--start` / `-Start` は省略可
- **ビルド検出**: `lake build` 後に olean が変化した場合、次の `--send` / `-Send` で自動的にデーモンを再起動する
- **クラッシュ復旧**: デーモンが異常終了した場合、次の `--send` / `-Send` で自動復旧する

### バッチモード経由（レガシー）

Persistent モードが利用できない状況（CI/CD、ワンショット実行等）でのみ使用する。

```powershell
# Windows — JSONL ファイルを渡してバッチ実行
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands-<sessionId>-<topic>-<runId>.jsonl

# macOS / Linux
.github/skills/lean-repl/scripts/repl.sh --input Scratch/commands-<sessionId>-<topic>-<runId>.jsonl
```

### lake exe repl を直接使う場合

> ⚠️ **直接実行では Unicode が文字化けする**: `[Console]::OutputEncoding` が CP932（日本語 Windows デフォルト）のままになるため、`ℕ`・`⊢`・`≤` 等が `?` に化ける。通常は `repl.ps1` 経由での実行を推奨。直接使う場合の対策は [`powershell-utf8-guide.md`](powershell-utf8-guide.md) を参照。

```powershell
# 単発コマンド（S2IL なし）
'{"cmd": "#eval 1 + 1"}' | lake exe repl

# ファイルから読み込む
Get-Content Scratch/commands-<sessionId>-<topic>-<runId>.jsonl | lake exe repl
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

## 自動先頭挿入による環境初期化

REPL スクリプトはデフォルトで `import S2IL\nimport Mathlib.Tactic\nimport Plausible\nimport Duper` を先頭コマンドとして自動追加する。
この自動先頭挿入により `env: 0` には S2IL + Mathlib.Tactic + Plausible + Duper が利用可能な環境が作られる。
`ring` / `linarith` / `exact?` / `#leansearch` / `#loogle` など全ての Mathlib タクティク、`plausible` タクティク（任意命題のランダムテスト）、および `duper` タクティク（超位置推論 ATP）が使える。

### 起動時間

初回は `import` が走るため `~11–20s` かかる。2 回目以降は Lean が `.olean` キャッシュを使用するため速くなる。

### `-NoPickle` フラグ（上級者向け）

先頭への自動挿入を抑制し、JSONL 内でインポートを完全に自己管理したい場合に使う。

> ⚠️ **`-NoPickle` の `env:0` は空環境（何もインポートされていない）**。通常モードの `env:0`（`import S2IL + Mathlib.Tactic + Plausible + Duper` 読み込み済）とは**意味が異なる**。JSONL の 1 行目に `import` コマンドを書き、その応答（`env:0`）を以降のコマンドの `"env": 0` として使うこと。

```powershell
# 自動先頭挿入なし（JSONL 内に import 文を書く）
.github/skills/lean-repl/scripts/repl.ps1 -NoPickle -InputFile Scratch/commands-<sessionId>-<topic>-<runId>.jsonl
```

### pickle（.olean キャッシュ）について

batch モードはデフォルトで `import S2IL` + `import Mathlib.Tactic` + `import Plausible` + `import Duper` を直接実行する（pickle は使用しない）。
pickle ファイル（`.repl/s2il.olean`）は旧実装の残骸であり、現在は読み込まれない。

---

## エージェント向けユースケース集

### [UC-1] 単発 `#eval` による高速反例チェック

```jsonl
{"cmd": "#eval toString Color.red", "env": 0}
```

上記を `Scratch/commands-<sessionId>-<topic>-<runId>.jsonl` に保存して:
```powershell
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands-<sessionId>-<topic>-<runId>.jsonl
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
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands-<sessionId>-<topic>-<runId>.jsonl
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

### スクリプト出力仕様（`-Send` / `-InputFile` 共通）

- **stdout**: 各 REPL 応答が **1 行 JSON** として出力される（複数行プリティプリントは自動圧縮）
- **stderr**: ビルドメッセージ・ステータスメッセージ（JSON ではない）
- **終了コード**: `0`=正常（全証明完了）, `1`=REPL 応答にエラーあり, `2`=REPL クラッシュ
- クラッシュ時は最終行に `{"error":"repl_crashed","message":"...","commands_sent":N,"responses_received":M}` が出力される
- **exit 1 の条件**: `messages[*.severity=="error"]`、`message` フィールドあり（tactic エラー）、`goals` 配列非空（証明未完了）のいずれか

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

`goals: []` → 証明完了。`goals` 非空 → 証明未完了（exit 1）。

> **多段階証明の中間ステップについて**: `intro h` 等でゴールが残った場合も exit 1 となるのは正常動作。
> 証明が完了したか否かは **`goals == []`** を直接確認すること。exit code のみに頼ると誤判定しうる。
> sorry → intro → simp_all のような段階的証明では、最終タクティクの応答の `goals` を確認すること。

### unpickle 応答

```json
{"env":0}
```

`env: 0` が S2IL 読み込み済み環境。以降のコマンドには `"env": 0` を指定する。

デフォルトモードでは自動先頭挿入で `env: 0` が作成されるため、JSONL 内で `unpickleEnvFrom` を書く必要はない。

---

## Gotchas と制限事項

### Lean タクティク・証明上の Gotchas（SKILL.md から移動）

#### Gotcha A: `rw` が関数引数の内側では失敗する

ゴールが `¬ (someFunc expr).isEmpty` のように、書き換えたい `expr` が「関数適用の引数の内側」にある場合、`rw [h]` は失敗する。

```lean
-- ❌ 失敗例: .isEmpty の引数内の expr を h で書き換えようとする
rw [h]           -- "motive is not type correct" または "did not converge"

-- ✅ 正しい対処: ▸ 演算子を使う
exact h ▸ original_proof  -- h : a = b を使って型レベルで書き換え

-- ✅ 代替: conv を使ってピンポイント書き換え
conv in expr => rw [h]
```

**適用場面**: `Gravity.placeFallingUnit`・`List.foldl` のように `def` で定義された関数の引数位置にある変数を書き換えたいとき。

---

#### Gotcha B: `#eval do` 内の `for x in xs` が ForIn エラーになる

`#eval do for x in (xs : List T) do ...` は型推論が曖昧になり `ForIn` インスタンス未発見エラーになることがある。

```lean
-- ❌ 失敗例
#eval do
  for x in (myList : List Nat) do
    IO.println (toString x)

-- ✅ 正しい対処: 戻り型を明示する
#eval show IO Unit from do
  for x in (myList : List Nat) do
    IO.println (toString x)
```

**追加注意**: 全シェイプ列挙・大規模 `#eval` は REPL ではタイムアウトしやすい。`Scratch/MyFile.lean` に書いて `lake env lean --run Scratch/MyFile.lean` で実行すること。

---

#### Gotcha C: Verification スクリプトに早期終了ロジックを組み込む

全シェイプ列挙で偽定理の反例を探す場合、反例が N 件見つかった時点で即座に終了する早期終了ロジックを必ず組み込む。

```lean
-- ✅ 推奨パターン: maxFails を設定して early exit
let maxFails := 10
let mut fails := 0
for shape in allShapes do
  if not (property shape) then
    fails := fails + 1
    IO.println s!"FAIL: {shape}"
    if fails >= maxFails then
      IO.println "maxFails reached, stopping early"
      break
```

**規則**: verify スクリプトは必ず `maxFails : Nat := 10` の early exit を含めること。

---

#### Gotcha D: `#eval` 記述前の API 確認チェックリスト

`#eval do` ブロックを作成する前に、使用する API が存在することを `#check` で確認する。

| 誤ったアクセス | 正しいアクセス | 理由 |
|---|---|---|
| `p.layer` | `QuarterPos.layer p` | ドット記法は型不明時にフィールド未解決 |
| `u.minLayer` | `FallingUnit.minLayer u` | 同上 |
| `xs.enum` | `xs.enumFrom 0` または `List.zipIdx xs` | `List` に `.enum` は存在しない |
| `arr[i]` | `arr.get? i` または `arr.getD i default` | 境界チェックが必要 |

**前確認手順**: `#check TypeName.fieldName` → `#check (inferInstance : ...)` → `#eval` ブロック作成の順で実施。

---


|---|---|
| **タクティクが証明を封じられず `goals != []` で exit 1** | `intro h` 等の中間タクティクでゴール残ありも exit 1。証明完了の判定は **`goals == []`** を直接確認すること。段階的証明では最終タクティクの応答を確認 |
| **コマンド間の区切りが空行でない**（`lake exe repl` 直接使用時） | `lake exe repl` を直接使う場合のみ必要。`repl.ps1` 経由では **Persistent モード**（`-Send`）が 1 行 1 コマンドに自動分割し、**バッチモード**（`-InputFile`）が空行区切りへ自動正規化するため、スクリプト経由では JSONL に空行を書かなくても動作する |
| `import` コマンドを `env` 指定と同時に使うとエラー | `import` は `env` なしコマンドのみ使用可。デフォルトモードでは自動先頭挿入が `env: 0` を作るので JSONL に `import` を書く必要はない |
| `repl_crashed`（S2IL ビルド失敗・JSONL 不正等） | JSONL の空行区切りを確認。`lake build` で S2IL のビルド状態を確認する |
| tactic mode の完了 proof state は現状 env に反映できない | tactic が成功しても `env` は更新されない。完全な証明は元ファイルに書く |
| scoped notation を pickle に含めると正しく復元されない場合がある | scoped 宣言は pickle 後のセッションで改めて定義する |
| REPL は stdin 読み込みが終わるまで応答しない場合がある | JSONL ファイルを `-InputFile` で渡す方が安定 |
| `sorry` を含む定理の `#eval` 結果は信頼できない | 反例チェックは sorry のない状態で行う |
| **`open S2IL in` が "unknown namespace" エラーになる** | `S2IL` はモジュール名であり Lean 名前空間ではない。`import S2IL` 後は `Color`, `Direction`, `GameConfig` 等がグローバルに参照可能。個別名前空間を開くには `open Color in` を使う |
| **【PowerShell】`-Input` 代わりに `-InputFile` を使う** | `-Input` は PowerShell の `$input` 自動変数（パイプライン列挙子）と衝突する。スクリプトパラメータは `-InputFile` |
| **【PowerShell】`pickleTo` 応答に `messages` フィールドがなく StrictMode 例外が発生する** | 応答 JSON と `$obj.messages` 等を参照する前に `$obj.PSObject.Properties['messages']` で存在確認する。`Set-StrictMode -Version Latest` 環境では必須 |
| **`#check` に存在しない宣言名を渡すと REPL がクラッシュ** | 補題検索（`exact?` / `#leansearch` 等）で確認した名前のみ `#check` に渡す |
| **REPL 出力のゴール文字列で `ℕ`, `⊢`, `≤` 等が `?` に化ける** | `lake exe repl` を `repl.ps1` 経由ではなく直接呼び出している場合。`repl.ps1` 経由では `StandardInputEncoding`・`[Console]::OutputEncoding` が UTF-8 に自動設定される |
| **【PowerShell】Persistent モード `-Send` の出力を変数やパイプでキャプチャできない** | `-Send` の出力は `[Console]::WriteLine()` で直接 stdout に書き込まれるため、`$var = repl.ps1 -Send ...` や `\| Set-Content` ではキャプチャできない。env/proofState は自動リベースされるため、各 CmdFile 内ではバッチモードと同じ番号付けが使える |
| **【Persistent】sorry の proofState を別バッチから参照できない** | proofState はバッチスコープ（各 `-Send` 呼び出し内）でのみ有効。sorry と tactic 試行は必ず同一バッチ（同一 `-CmdFile`）内で完結させること。別バッチで `proofState: 0` を送ると、リベースにより異なる proofState ID が REPL に送信され "Unknown proof state" エラーになる |
| **【PowerShell】`-Cmd` と `-CmdFile` の同時指定** | 両方指定した場合、`-CmdFile` が優先される（警告が表示される）。`-Cmd` は無視される |
| **【PowerShell】`-Cmd` に改行を含む Lean コードは渡せない** | PowerShell の引数では実際の改行は引数終端になる。改行（`\n`）を含む場合は `-CmdFile` でファイル渡しにする。`-Cmd` はシングルクォート内に改行もシングルクォートも含まない単純コマンド（`#eval`・単一 tactic 等）にのみ使う |
| **【PowerShell】`-Cmd '...'` にシングルクォートを含む Lean コードは注意** | PowerShell のシングルクォート文字列内でシングルクォートを表現するには `''` と書く必要がある。Lean のシングルクォート（`'` 付き変数名等）を含む場合は `-CmdFile` を使う方が安全 |
| **【PowerShell】`.ps1` スクリプトへの `--` / `--%`（stop-parsing）は使えない** | bash の `--` や PowerShell の `--%` は外部実行ファイルへのネイティブコマンド呼び出しにのみ効く。`.ps1` スクリプトのパラメータ解析には**効かない**。エスケープ問題の回避策は常にファイル渡し（`-CmdFile`）を使うこと |
| **`private theorem` が "Unknown identifier" になる** | `private` はモジュール外から不可視。REPL は `import S2IL` した別モジュールとして動作するため、`private` 定義には REPL からアクセスできない。`private` → `protected` に変更してから FQN（`#check @Namespace.lemmaName`）でアクセスする |

---

## REPL 入力の Unicode 記法 / ASCII fallback テーブル

### Unicode サポート状況

`repl.ps1` 経由でのバッチ・Persistent モードのいずれも、Unicode 文字をそのまま JSONL に入力できる。
- `$psi.StandardInputEncoding = UTF8`（daemon stdin）
- `[Console]::OutputEncoding = UTF8`（batch/send の stdout 出力）
の設定が自動適用されるため、`ℕ`、`⊢`、`≤`、`≥`、`¬` 等が正しく送受信される。

**ASCII fallback**（旧来の記法）は引き続き使えるが、必須ではない。長い型名（`Nat` vs `ℕ`）は可読性を考慮して選択する。

### 変換テーブル

### Unicode / ASCII 等価表（参考）

Unicode と ASCII-fallback の対応表。どちらを使っても動作するが、可読性を重視して選択する。

#### 型・宇宙

| Unicode（推奨） | ASCII fallback | 備考 |
|---|---|---|
| `ℕ` | `Nat` | 自然数型 |
| `ℤ` | `Int` | 整数型 |
| `ℝ` | `Real` または `Float` | 実数（Mathlib か Float か用途に応じて） |
| `α`, `β`, `γ` | `α`, `β`, `γ` (そのまま) | 型変数 |

#### 論理

| Unicode（推奨） | ASCII fallback | 備考 |
|---|---|---|
| `∧` | `And a b` または中置 `a /\ b` | 命題論理の積 |
| `∨` | `Or a b` または `a \/ b` | 命題論理の和 |
| `¬` | `Not` または `!` | 否定 |
| `↔` | `Iff` | 同値 |
| `∀ x, p x` | `(x : _) -> p x` | 全称量化 |
| `∃ x, p x` | `Exists` | 存在量化子 |

#### 矢印・比較

| Unicode（推奨） | ASCII fallback | 備考 |
|---|---|---|
| `→` | `->` | 関数型・含意 |
| `←` | `<-` | 逆方向（`rw` の引数等） |
| `≤` | `LE.le` または `Nat.ble` | 以下 |
| `≥` | `GE.ge` | 以上 |
| `≠` | `Ne` | 不等号 |

#### 集合・リスト

| Unicode（推奨） | ASCII fallback | 備考 |
|---|---|---|
| `∈` | `List.elem` / `Finset.mem` | 帰属関係（型による） |
| `∩` | `Finset.inter` / `Set.inter` | 積集合 |
| `∪` | `Finset.union` / `Set.union` | 和集合 |
| `⊆` | `Finset.Subset` / `Set.Subset` | 部分集合 |
| `∅` | `Finset.empty` または `{}` | 空集合 |

#### その他

| Unicode（推奨） | ASCII fallback | 備考 |
|---|---|---|
| `⟨a, b⟩` | `Prod.mk a b` | 積・構造体コンストラクタ |
| `⊢` | （出力にのみ現れる） | ゴール区切り記号 |
| `·` | `fun _ => ...` | 無名引数 |

### 使用例

```jsonl
-- ✅ Unicode 記法（推奨）
{"cmd": "theorem foo (n : ℕ) : n ≤ n + 1 := by omega", "env": 0}

-- ✅ ASCII fallback も動作
{"cmd": "theorem foo (n : Nat) : n <= n + 1 := by omega", "env": 0}
```

---

## セッション終了時の `.repl/` クリーンアップ

REPL セッション終了時（ユーザーの作業完了宣言後）、以下を実施する:

1. Persistent セッションの停止: `repl.ps1 -Stop -SessionId <id>`
2. `.repl/` ディレクトリの stale セッションクリーンアップ:

```powershell
# Windows — 7 日以上古いセッションディレクトリを削除
Get-ChildItem .repl/ -Directory | Where-Object { $_.LastWriteTime -lt (Get-Date).AddDays(-7) } | Remove-Item -Recurse
Get-ChildItem .repl/ -File | Where-Object { $_.LastWriteTime -lt (Get-Date).AddDays(-7) } | Remove-Item
```

```bash
# macOS / Linux
find .repl/ -maxdepth 1 -type d -mtime +7 -exec rm -rf {} +
find .repl/ -maxdepth 1 -type f -mtime +7 -delete
```

---

## REPL → .lean 移植ワークフロー 詳細

### transplant-proof.ps1 / transplant-proof.sh オプション

```powershell
# Windows — 主要オプション
.github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -ProofFile Scratch/proof.lean
.github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -Proof "by omega"
.github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -ProofFile Scratch/proof.lean -SimpStabilize
.github/skills/lean-repl/scripts/transplant-proof.ps1 -File S2IL/Foo.lean -Line 42 -ProofFile Scratch/proof.lean -DryRun
```

```bash
# macOS / Linux
.github/skills/lean-repl/scripts/transplant-proof.sh --file S2IL/Foo.lean --line 42 --proof-file Scratch/proof.lean
.github/skills/lean-repl/scripts/transplant-proof.sh --file S2IL/Foo.lean --line 42 --proof "by omega"
.github/skills/lean-repl/scripts/transplant-proof.sh --file S2IL/Foo.lean --line 42 --proof-file Scratch/proof.lean --simp-stabilize
```

**処理内容**: sorry 行のインデントを自動検出 → 証明テキストに適切なインデントを適用 → sorry を置換 → UTF-8 BOM なしで書き込み。`-SimpStabilize` 指定時は `simp-stabilize.ps1` を chain 実行。

### simp 安定化の戦略

| タイミング | 手法 | メリット |
|---|---|---|
| **REPL 証明中**（推奨） | `simp?` で `Try this:` を回収 → `simp only [...]` で証明を仕上げる | 移植後の修正サイクルが 0 |
| **移植時**（是正） | `-SimpStabilize` で `simp-stabilize.ps1` を chain 実行 | 1 ステップで一括変換 |
| **移植後**（レガシー） | `simp-stabilize.ps1 -File <path>` を手動実行 | 個別対処 |

