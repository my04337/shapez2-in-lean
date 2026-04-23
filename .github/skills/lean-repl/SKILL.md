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

# Lean REPL スキル

JSONL コマンドを Lean 4 REPL に送り、`import S2IL + Mathlib.Tactic + Plausible + Duper` 済み環境で即時評価する。

## 発動除外

- 既存補題のリネーム・構造分割のみ
- 使用 API が同ファイル内で型確認不要
- `simp only` 調整のみ（`lean-simp-stabilizer` を使う）

## Quick Reference

```jsonl
{"cmd": "#eval 1 + 1", "env": 0}

{"cmd": "theorem test : 1 + 1 = 2 := by norm_num", "env": 0}

{"cmd": "example : ∀ n : Nat, n + 0 = n := by sorry", "env": 0}
```

- 各コマンドは**空行で区切る**（区切りなしはパースエラー）
- `import` 不要（自動先頭挿入）
- 最初のコマンドは `"env": 0`、以降は前応答の `env` を使う
- コマンドファイルは `Scratch/commands-<sessionId>-<topic>-<runId>.jsonl`（毎回一意化）
- Unicode (`ℕ ⊢ ≤ ∀`) はそのまま使用可

`ring` / `linarith` / `norm_num` / `exact?` / `apply?` / `aesop` / `plausible` / `duper` が自動利用可。詳細: [`references/repl-guide.md`](references/repl-guide.md)

## REPL → 本体ファイル移植の注意

REPL は `Mathlib.Tactic` を自動 import するが、本体ファイルにないとビルド失敗する。移植前に対象ファイルの import を確認し、必要なら `Mathlib.Tactic` 追加か `omega` 等の代替に置換する。

## スクリプト（Persistent モード推奨・~600ms/回）

通常の証明作業・反例チェック・タクティク探索はこのモードを使う。初回 import ~13s、以降は再利用。

```powershell
# セッション開始
.github/skills/lean-repl/scripts/repl.ps1 -Start -SessionId <id>

# コマンド送信（ファイル or 単発）
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -CmdFile Scratch/commands-<sessionId>-<topic>-<runId>.jsonl
.github/skills/lean-repl/scripts/repl.ps1 -Send -SessionId <id> -Cmd '{"cmd": "#eval 1 + 1"}'

# 停止
.github/skills/lean-repl/scripts/repl.ps1 -Stop -SessionId <id>
```

（macOS/Linux は `.sh` 版を使う。引数は `--start` / `--send --session-id` / `--cmd-file` / `--cmd` / `--stop`）

### 自動機能

- Lazy Start: `-Send` 時にデーモン未起動なら自動起動
- ビルド検出: olean ハッシュ変化で自動再起動
- クラッシュ復旧: 次の `-Send` で自動復旧
- 冪等性: 起動済みへの `-Start` は安全
- env/proofState リベース: バッチ内では `env: 0`=import 環境、`env: 1`=最初のコマンド結果、`proofState: 0`=最初の sorry ゴール

### バッチ間の分離

各 `-Send` バッチは独立した env・proofState 空間を持つ。sorry とその tactic 試行は**同一バッチ**内で完結させる。

### エラー復旧

1. `-Stop -SessionId <id>`
2. `-Start -SessionId <id>`
3. 続く場合は SessionId を変えて再試行

Persistent モードから Batch への永続切替は禁止（Persistent と Pickle は独立）。

### Private 定義へのアクセス

`namespace ... end` で囲むか、`Scratch/*.lean` + `open ModuleName` で `lake env lean Scratch/MyFile.lean` を使う。

### 出力キャプチャの注意

`-Send` の出力は `[Console]::WriteLine()` で直接 stdout に書かれるため、`$var = repl.ps1 -Send ...` や `| Tee-Object` でキャプチャ不可。

`-Cmd` と `-CmdFile` を両方指定した場合は `-CmdFile` が優先される。

### バッチモード（レガシー・~15-20s/回）

CI/CD 等で Persistent が使えない場合のみ:

```powershell
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands-<sessionId>.jsonl
```

`lean-run`（`run.ps1`）は `lake exe <Target>` 実行用で JSONL 評価には使わない。

## 出力仕様

- stdout: 各応答は 1 行 JSON
- stderr: ビルド・ステータスメッセージ
- 終了コード: `0`=正常 / `1`=エラー / `2`=クラッシュ
- クラッシュ時: `{"error":"repl_crashed","commands_sent":N,"responses_received":M}`
- exit 1 の条件: `messages[*].severity=="error"` または `message` フィールド（tactic エラー）。`goals != []` は exit 0（証明未完了でもエラーではない）

### 応答フィールド

| フィールド | 説明 |
|---|---|
| `env` | 次回使える環境 ID |
| `messages[].severity` | `info` / `warning` / `error` |
| `messages[].data` | `#eval` 出力・エラー文字列 |
| `sorries[].goal` | sorry のゴール文字列 |
| `sorries[].proofState` | tactic mode に移行する proofState ID |
| `goals` | tactic mode ゴール一覧（`[]`=完了） |
| `message` | tactic 失敗等のエラー文字列 |

## 典型パターン

### 反例チェック / #eval

```jsonl
{"cmd": "#eval ([Quarter.crystal Color.red, Quarter.pin] : List Quarter)", "env": 0}
```

1 行目 `{"env":0}` は自動 import 応答、2 行目以降がユーザー応答。

### sorry ゴール確認 → タクティク探索

```jsonl
{"cmd": "theorem foo (n : Nat) : n + 0 = n := by sorry", "env": 0}
```

応答の `sorries[0].proofState` を使ってタクティクを空行区切りで試す:

```jsonl
{"tactic": "simp", "proofState": 0}

{"tactic": "omega", "proofState": 0}

{"tactic": "ring", "proofState": 0}
```

完了: `{"proofStatus":"Completed","goals":[]}` / 未完了: `goals` にゴール文字列あり。同一 `proofState` に複数タクティクをバッチ投入して並列探索可。

## `lake exe repl` を直接使う場合

各コマンドを**空行で区切る**こと（`repl.ps1` / `repl.sh` 経由なら自動正規化されるため不要）。
