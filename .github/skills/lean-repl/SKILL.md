---
name: lean-repl
description: >
  Interactively evaluate Lean 4 snippets, tactics, and counterexamples via REPL
  (auto-imports S2IL + Mathlib.Tactic + Plausible + Duper).
  Use when: interactive eval, quick snippet check, tactic step exploration, sorry goal inspect,
  fast counterexample, repl session, lean repl, tactic mode, proofState, pickle env,
  eval without full build, instant lean check.
metadata:
  argument-hint: 'Pass Lean snippet for immediate REPL evaluation'
---

## 発動除外条件（これらに該当する場合は本スキルをロードしない）

- 既存の private/public 補題を純粋に構造分割・リネームするだけのリファクタリング
- 使用する API がすべて同ファイル内に定義済みで型確認が不要な場合
- `simp only` 複層の調整のみ（これは lean-simp-stabilizer エージェントを使う）

# Lean REPL スキル

## Quick Reference（最小限のフォーマット）

```jsonl
{"cmd": "#eval 1 + 1", "env": 0}

{"cmd": "theorem test : 1 + 1 = 2 := by norm_num", "env": 0}

{"cmd": "example : ∀ n : Nat, n + 0 = n := by sorry", "env": 0}
```

**必須ルール**:
- 各コマンドは **空行で区切る**（区切りなし→パースエラー）
- `import` 不要（スクリプトが `import S2IL + Mathlib.Tactic + Plausible + Duper` を自動先頭挿入）
- 最初のコマンドは `"env": 0`、以降は前の応答の `env` 値を使う
- ファイルは `Scratch/commands-<sessionId>.jsonl` に配置（セッション ID は SessionStart フックの systemMessage から取得。不明な場合は `Scratch/commands.jsonl` にフォールバック）
- Unicode 文字（`ℕ`、`⊢`、`≤`、`∀` 等）はそのまま JSONL に使用できる（バッチ・Persistent 両モードで UTF-8 完全サポート）

---

デフォルトで `import S2IL + Mathlib.Tactic + Plausible + Duper` を先頭に自動挿入して起動する（~11-20s）。
`ring`, `linarith`, `nlinarith`, `norm_num`, `exact?`, `apply?`, `funext`, `simp?` 等
すべての Mathlib タクティク、`aesop` タクティク（ルールベース自動証明。S2IL の等変性補題が `@[aesop norm simp]` 登録済み）、`plausible` タクティク（任意命題のランダムテスト）、および `duper` タクティク（超位置推論 ATP）をそのまま使える。
詳細は [`references/repl-guide.md`](references/repl-guide.md) を参照。

## ユースケース早見表

> このスキルは「REPL でスニペットを実行する」だけでなく、以下の多様な用途で利用できる。

| 状況・やりたいこと | 使う手法 | 詳細 |
|---|---|---|
| `#eval` で式・値を即時確認したい | Command mode + `#eval` | UC-1 |
| 複数の式・反例をまとめて検証したい | バッチ Command mode | UC-2 |
| sorry のゴール状態を確認したい | sorry 投入 → `sorries[0].goal` 参照 | UC-3 |
| 同じゴールに複数タクティクを一斉試行したい | 同一 `proofState` に複数 tactic 投入 | UC-4 |
| 証明を段階的に組み立てたい | step-by-step tactic（分岐ごとに `proofState`） | UC-5 |
| Mathlib 補題の型シグネチャを確認したい | `#check` | UC-6 |
| 型クラスインスタンスの存在を確認したい | `#check (inferInstance : ...)` | UC-7 |
| 自然言語で Mathlib 定理を探したい | `#leansearch "..."` | UC-8 |
| 型パターンで Mathlib 定理を探したい | `#loogle "..."` | UC-8 |
| ゴールを閉じる補題を見つけたい | tactic mode + `exact?` | UC-8 |
| 適用可能な形の補題を探したい | tactic mode + `apply?` | UC-8 |
| `private theorem` が "Unknown identifier" になる | WIP フロー（`protected` + `-- [WIP]`）で FQN アクセスに変換 | — |

UC 番号は `references/repl-guide.md` のユースケース集に対応する。

## スクリプト

### Persistent モード（推奨・~600ms/回）

REPL プロセスを常駐させ、2回目以降の呼び出しを ~600ms に短縮する。
初回のみ import に ~13s かかるが、以降はプロセス再利用で高速応答。
**通常の証明作業・反例チェック・タクティク探索ではこのモードを使うこと。**

```powershell
# Windows — セッション開始（import 完了まで待機。初回 ~13s）
.github/skills/lean-repl/scripts/repl.ps1 -Start -SessionId <id>

# コマンド送信（~600ms）— 応答は stdout に 1 行 JSON で出力
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands.jsonl
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -Cmd '{"cmd": "#eval 1 + 1"}'

# セッション停止
.github/skills/lean-repl/scripts/repl.ps1 -Stop -SessionId <id>
```

```bash
# macOS / Linux — セッション開始（bash 4+ 必須）
.github/skills/lean-repl/scripts/repl.sh --start --session-id <id>

# コマンド送信（~600ms）— 応答は stdout に 1 行 JSON で出力
.github/skills/lean-repl/scripts/repl.sh --send --session-id <id> --cmd-file Scratch/commands.jsonl
.github/skills/lean-repl/scripts/repl.sh --send --session-id <id> --cmd '{"cmd": "#eval 1 + 1"}'

# セッション停止
.github/skills/lean-repl/scripts/repl.sh --stop --session-id <id>
```

| オプション (Windows) | オプション (macOS/Linux) | 説明 |
|---|---|---|
| `-Start -SessionId <id>` | `--start --session-id <id>` | デーモン起動。import 完了まで待機 |
| `-Send -SessionId <id> -CmdFile <path>` | `--send --session-id <id> --cmd-file <path>` | ファイルからコマンド送信（JSONL 形式） |
| `-Send -SessionId <id> -Cmd '<json>'` | `--send --session-id <id> --cmd '<json>'` | 単一コマンド送信 |
| `-Stop -SessionId <id>` | `--stop --session-id <id>` | デーモン停止・セッションクリーンアップ |

**自動機能**:
- **Lazy Start**: `-Send` 時にデーモン未起動なら自動起動
- **ビルド検出**: `lake build` 後に olean ハッシュ変化を検出し、自動再起動
- **クラッシュ復旧**: デーモン死亡時は次の `-Send` で自動復旧
- **冪等性**: 起動済みセッションへの `-Start` は安全（既存セッションを再利用）
- **env/proofState 自動リベース**: 各 `-Send` バッチ内の `env` (> 0) と `proofState` を入力・応答の両方向で自動的にリベースする。バッチ内では常に `env: 0`=import 環境、`env: 1`=最初のコマンドの結果、`proofState: 0`=バッチ内最初の sorry のゴール、として記述でき、応答も同じバッチ内相対値で返される
- **バッチ間の env/proofState 分離**: 各 `-Send` バッチは独立した env・proofState 空間を持つ。あるバッチで `def` した定義を別のバッチから `env: 0` で参照することはできない。**同様に、あるバッチの sorry の proofState を別のバッチから参照することもできない。** sorry とその tactic 試行は必ず同一バッチ（同一 `-CmdFile` / 同一 `-Send`）内で完結させること

**エラー復旧フロー**:

Persistent モードでエラーが発生した場合、以下の手順で復旧する。**Batch への永続的切り替えは禁止。**

1. `-Stop -SessionId <id>` でセッション停止
2. `-Start -SessionId <id>` で再起動
3. 再起動後も問題が続く場合、SessionId を変えて再試行

Persistent モードは Pickle と**独立**した常駐プロセス方式で動作する。Pickle のエラーは Persistent モードの使用可否に影響しない。

```
# ✅ Persistent モードのエラー復旧
repl.ps1 -Stop -SessionId my-session
repl.ps1 -Start -SessionId my-session   # 再起動

# ❌ 誤解: Pickle エラー → Persistent 放棄 → Batch に永続切替
# Pickle と Persistent は独立。Pickle エラー時も Persistent は使用可能
```

**Private 定義へのアクセス**:

REPL で `private def` / `private theorem` にアクセスする場合は、以下のいずれかを使う:

- `namespace ModuleName ... end ModuleName` で囲む
- `Scratch/*.lean` ファイル + `open ModuleName` で実行（`lake env lean Scratch/MyFile.lean`）

> **⚠️ `-Send` の出力はキャプチャ不可**: `-Send` の出力は `[Console]::WriteLine()` で直接 stdout に書き込まれる。
> `$var = repl.ps1 -Send ...` や `| Tee-Object` ではキャプチャできない。
> env/proofState の自動リベースにより、各 CmdFile 内では常にバッチモードと同じ番号付けが使える。
> `-Cmd` で単一コマンドを送信する場合も同じリベースが適用される点に注意。

> **⚠️ `-Cmd` と `-CmdFile` の同時指定**: 両方指定した場合、`-CmdFile` が優先される（警告が表示される）。

### バッチモード（レガシー・~15-20s/回）

Persistent モードが利用できない状況（CI/CD、ワンショット実行等）でのみ使用する。

```powershell
# Windows — JSONL ファイルを渡してバッチ実行（デフォルト: import S2IL + Mathlib.Tactic + Plausible + Duper を自動先頭挿入）
# ⚠️ .jsonl ファイルは必ず Scratch/ ディレクトリに配置すること（.gitignore 管理）
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands-<sessionId>.jsonl
```

```bash
# macOS / Linux — JSONL ファイルを渡してバッチ実行
.github/skills/lean-repl/scripts/repl.sh --input Scratch/commands-<sessionId>.jsonl
```

| オプション (Windows) | オプション (macOS/Linux) | 説明 |
|---|---|---|
| `-InputFile <path>` | `--input <path>` | JSONL 入力ファイル（省略=インタラクティブ） |
| `-NoPickle` | `--no-pickle` | 自動先頭挿入なし（ユーザーが JSONL 内で `import` を管理する場合）。⚠️ このモードの `env:0` は**空環境**（何もインポートされていない）。通常モードの `env:0`（S2IL + Mathlib.Tactic 読み込み済み）とは意味が異なる |

## 出力仕様（両モード共通）

- **stdout**: 各 REPL 応答が **1 行 JSON**（複数行は自動圧縮）
- **stderr**: ビルド・ステータスメッセージ
- **終了コード**: `0`=正常, `1`=エラーあり, `2`=REPL クラッシュ
- クラッシュ時は最終行に `{"error":"repl_crashed","commands_sent":N,"responses_received":M}` を出力
- **exit 1 の条件**: `messages[*.severity=="error"]`、`message` フィールドあり（tactic エラー）のいずれか。`goals` 配列非空（証明未完了）は exit 1 に含まない
- **段階的証明の判定**: sorry ゴール確認や中間タクティク（`intro h` 等）で `goals != []` が返る場合も exit code は 0。証明完了 / 未完了の判定は、個別応答の `goals` フィールドを確認すること

### 応答フィールド

| フィールド | 説明 |
|---|---|
| `env` | 次回使用可能な環境 ID |
| `messages[].severity` | `info` / `warning` / `error` |
| `messages[].data` | `#eval` 出力やエラー文字列 |
| `sorries[].goal` | sorry のゴール文字列 |
| `sorries[].proofState` | tactic mode に移行する証明状態 ID |
| `goals` | tactic mode でのゴール一覧。`[]`=証明完了、非空=証明未完了。exit code には影響しない |
| `message` | tactic 失敗・Unknown proof state 等のエラー文字列 → 終了コード 1 |

## JSONL 入力パターン

> ⚠️ **`lake exe repl` を直接使う場合は各コマンドを空行（blank line）で区切ること。** 区切りなしでは REPL が複数コマンドを 1 つの JSON として解釈しパースエラーになる。
> **`repl.ps1` 経由では不要**（Persistent モード `-Send` は 1 行 1 コマンドに自動分割し、バッチモード `-InputFile` は空行区切りへ自動正規化する）。

スクリプトが `import S2IL + Mathlib.Tactic + Plausible + Duper` を先頭に自動挿入するため、JSONL の最初のコマンドは `"env": 0` で直接 S2IL の型・Mathlib タクティク・duper を使える。

### 反例チェック / #eval

```jsonl
{"cmd": "#eval ([Quarter.crystal Color.red, Quarter.pin] : List Quarter)", "env": 0}
```

▶ stdout 例（1コマンド1行）:

> ℹ️ **1行目 `{"env":0}` は自動挿入された import コマンドの応答**（ユーザーコマンドの応答は 2 行目以降）

```
{"env":0}
{"messages":[{"severity":"info","data":"[Quarter.crystal (Color.red), Quarter.pin]"}],"env":1}
```

### sorry ゴール確認 → タクティク探索

```jsonl
{"cmd": "theorem foo (n : Nat) : n + 0 = n := by sorry", "env": 0}
```

▶ stdout 例（`sorries[0].goal` でゴール確認）:

> ℹ️ **1行目 `{"env":0}` は自動挿入された import コマンドの応答**（ユーザーコマンドの応答は 2 行目以降）

```
{"env":0}
{"sorries":[{"proofState":0,"goal":"n : ℕ\n⊢ n + 0 = n"}],"env":1}
```

`sorries[0].proofState` の値でタクティクを試す（各タクティクも空行区切り）:

```jsonl
{"tactic": "simp", "proofState": 0}

{"tactic": "omega", "proofState": 0}

{"tactic": "ring", "proofState": 0}
```

▶ 証明完了: `{"proofStatus":"Completed","proofState":1,"goals":[]}` / 未完了: `goals` にゴール文字列あり  
同一 `proofState` に複数タクティクをバッチ投入して並列探索できる。

### タクティク対話的探索（step-by-step）

sorry のゴールに対して複数タクティクを効率的に試すパターン。
同一 `proofState` に対して複数タクティクをバッチ投入し、並列比較できる。

```jsonl
{"cmd": "theorem test (n m : Nat) (h : n < m) : n + 1 ≤ m := by sorry", "env": 0}
```

▶ 応答: `sorries[0].proofState: 0`, `sorries[0].goal: "n m : ℕ\nh : n < m\n⊢ n + 1 ≤ m"`

候補タクティクを一斉試行（各行を空行で区切る）:

```jsonl
{"tactic": "omega", "proofState": 0}

{"tactic": "simp_all", "proofState": 0}

{"tactic": "exact Nat.succ_le_of_lt h", "proofState": 0}
```

▶ 判定ルール:
- `goals: []` → **証明完了**（そのタクティクを採用）
- `goals` にゴール文字列あり → サブゴールが残る（部分的進展）
- `messages[].severity == "error"` → そのタクティクは不適用

段階的に深掘りする場合（タクティク A の後にタクティク B を試す）:

```jsonl
{"tactic": "change n.succ ≤ m", "proofState": 0}

{"tactic": "exact h", "proofState": 1}
```

`proofState` は前のタクティクの応答に含まれる `proofState` フィールドの値を使う。

### ファイル全体の評価

```jsonl
{"path": "Scratch/MyFile.lean", "allTactics": true}
```

## 注意事項

- **env: 0 は先頭に自動挿入された import の環境**: `import S2IL + Mathlib.Tactic + Plausible + Duper` が env: 0。以降のコマンドは `"env": 0` で指定する
- **`S2IL` は名前空間ではない**: `import S2IL` 後は `Color`, `Direction` 等がグローバル参照可能。`open S2IL in` は不要（エラーになる）
- **起動時間**: 初回起動時 ~11-20 秒（Mathlib .olean のキャッシュ読み込み）。既にキャッシュされた環境では短縮される
- **REPL クラッシュ**: 未処理コマンド数と共にクラッシュ JSON を出力。終了コード 2
- **`unpickleEnvFrom` を JSONL に含める場合**: スクリプトが先に import を挿入するため unpickle 環境は env: 1 になる。通常は不要

## PowerShell での UTF-8 安全な出力キャプチャ

**`repl.ps1` 経由では自動処理済み**: バッチ・Persistent 両モードで `[Console]::OutputEncoding` および `StandardInputEncoding` が UTF-8 に自動設定されるため、`ℕ`・`⊢`・`≤` 等の Unicode 文字はそのまま送受信できる。

`lake exe repl` を直接使う場合（スクリプト外）の文字化け対策は [`references/powershell-utf8-guide.md`](references/powershell-utf8-guide.md) を参照。

## REPL エラー診断

REPL が期待通りに動作しない場合、エラーメッセージから原因を特定する。

| エラーメッセージ | 原因 | 対処 |
|---|---|---|
| `Unknown constant` (`OfNat`, `Nat` 等の基本型) | `import` 失敗。S2IL のビルドエラーが原因 | `build.ps1` でビルド状態確認 → S2IL のエラー修正 |
| `offset N` parse error | JSONL のフォーマット不正（改行・エスケープ） | `commands-*.jsonl` の JSON 構文・空行区切りを確認 |
| `repl_crashed` (終了コード 2) | REPL プロセス異常終了（JSONL フォーマット不正が多い） | JSONL の空行区切りを確認。S2IL ビルドエラーも確認 |
| `unknown package` | lakefile 設定不整合 | `lake update` 実行 |
| ゴール文字列の `ℕ`, `⊢`, `≤` 等が `?` に化ける | スクリプト外から `lake exe repl` を直接呼び出している場合（`[Console]::OutputEncoding` が設定されていない） | `repl.ps1` 経由で実行すれば自動的に UTF-8 エンコーディングが設定される |

> **重要**: `Unknown constant` エラーが Prelude 相当の型（`OfNat`, `ToString` 等）で発生した場合、
> **REPL 自体の問題ではなく S2IL のビルドエラーが原因**。REPL スクリプトの調査ではなく、
> まず `build.ps1` を実行してビルド状態を確認すること。

## REPL デバッグ時のファイルベース実行

PowerShell のヒアストリング (`@'...'@`) やエスケープ (`""`, `\"`) で JSONL を構築すると、
以下の問題が頻発する:

- `@'...'@` の終端 `'@` が行頭にないとパースエラー
- `""` と `\"` の混在による JSON パース失敗
- 変数代入 (`$cmds = ...`) と実行 (`$cmds | lake exe repl`) が別のターミナル呼び出しに分離

これらを回避するため、REPL デバッグ時も **ファイルベース** で実行する:

1. セッション固有の JSONL ファイルに テストコマンドを書き込む（`create_file` / `replace_string_in_file`）
   - ファイル名: `Scratch/commands-<sessionId>.jsonl`（セッション ID は SessionStart フックの systemMessage から取得）
   - セッション ID が不明な場合: `Scratch/commands.jsonl` をフォールバックとして使用
2. `.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands-<sessionId>.jsonl` で実行
3. エラーを確認し、JSONL ファイルを書き換えて再実行

**禁止**: PowerShell 変数やヒアストリングで JSONL を構築してパイプに渡すパターン。

## セッション終了時の `.repl/` クリーンアップ

REPL セッション終了時（ユーザーの作業完了宣言後）、以下を実施する:

1. Persistent セッションの停止: `repl.ps1 -Stop -SessionId <id>`
2. `.repl/` ディレクトリの stale セッションクリーンアップ:

```powershell
# Windows — 7 日以上古いセッションディレクトリを削除
Get-ChildItem .repl/ -Directory | Where-Object { $_.LastWriteTime -lt (Get-Date).AddDays(-7) } | Remove-Item -Recurse
# stale な .olean / .tmp ファイルも削除
Get-ChildItem .repl/ -File | Where-Object { $_.LastWriteTime -lt (Get-Date).AddDays(-7) } | Remove-Item
```

```bash
# macOS / Linux — 7 日以上古いセッションディレクトリを削除
find .repl/ -maxdepth 1 -type d -mtime +7 -exec rm -rf {} +
find .repl/ -maxdepth 1 -type f -mtime +7 -delete
```

## よくある落とし穴（Gotchas）

### Gotcha A: `rw` が関数適用の引数位置で失敗する

ゴールが `¬ (someFunc expr).isEmpty` のように、書き換えたい `expr` が「関数適用の引数の内側」にある場合、`rw [h]` は失敗する。これは Lean 4 の `rw` の制約（デファースに依存するパターンマッチ）によるもの。

```lean
-- ❌ 失敗例: .isEmpty の引数内の expr を h で書き換えようとする
rw [h]           -- "motive is not type correct" または "did not converge"
simp only [h]    -- 同様に失敗する場合がある

-- ✅ 正しい対処: ▸ 演算子を使う
exact h ▸ original_proof  -- h : a = b を使って型レベルで書き換え

-- ✅ 代替: unfold で展開してから ▸
unfold SomeFunc
exact h ▸ h_ne

-- ✅ 代替: conv を使ってピンポイント書き換え
conv in expr => rw [h]
```

**適用場面**: `Gravity.placeFallingUnit`・`List.foldl` のように、`def` で定義された関数の引数位置にある変数を書き換えたいとき。

---

### Gotcha B: `#eval do` 内の `for x in xs` が ForIn エラーになる

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

-- ✅ 代替: Array.forM を使う
#eval (myList : List Nat).toArray.forM (fun x => IO.println (toString x))
```

**追加注意**: 全シェイプ列挙・大規模 `#eval` は REPL ではタイムアウトしやすい。最初から `Scratch/MyFile.lean` に書いて `lake env lean --run Scratch/MyFile.lean` で実行すること。
