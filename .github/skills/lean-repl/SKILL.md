---
name: lean-repl
description: >
  Lean 4 REPL (leanprover-community/repl) を使ってスニペット・タクティク・反例を
  対話的に即時評価する。デフォルトで import S2IL + Mathlib.Tactic を自動適用し、
  ring, linarith, exact?, funext 等すべての Mathlib タクティクを即座に利用できる。
  Use when: interactive eval, quick snippet check, tactic step exploration, sorry goal inspect,
  fast counterexample, repl session, lean repl, tactic mode, proofState, pickle env,
  eval without full build, instant lean check.
metadata:
  argument-hint: 'Lean REPL セッションでスニペットを即時評価します'
---

# Lean REPL スキル

デフォルトで `import S2IL + Mathlib.Tactic` を自動プレペンドして起動する（~11-20s）。
`ring`, `linarith`, `nlinarith`, `norm_num`, `exact?`, `apply?`, `funext`, `simp?` 等
すべての Mathlib タクティクをそのまま使える。
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

UC 番号は `references/repl-guide.md` のユースケース集に対応する。

## スクリプト

```powershell
# JSONL ファイルを渡してバッチ実行（デフォルト: import S2IL + Mathlib.Tactic を自動プレペンド）
# ⚠️ .jsonl ファイルは必ず Scratch/ ディレクトリに配置すること（.gitignore 管理）
.github/skills/lean-repl/scripts/repl.ps1 -InputFile Scratch/commands.jsonl

# pickle を再生成（カスタムセッション保存用。通常は不要）
.github/skills/lean-repl/scripts/repl.ps1 -RebuildPickle
```

| オプション | 説明 |
|---|
| `-InputFile <path>` | JSONL 入力ファイル（省略=インタラクティブ） |
| `-RebuildPickle` | pickle を再生成（カスタム状態保存用） |
| `-NoPickle` | 自動プレペンドなし（ユーザーが JSONL 内で import/unpickle を管理する場合） |

## 出力仕様（`-InputFile` モード）

- **stdout**: 各 REPL 応答が **1 行 JSON**（複数行は自動圧縮）
- **stderr**: ビルド・ステータスメッセージ
- **終了コード**: `0`=正常, `1`=エラーあり, `2`=REPL クラッシュ
- クラッシュ時は最終行に `{"error":"repl_crashed","commands_sent":N,"responses_received":M}` を出力

### 応答フィールド

| フィールド | 説明 |
|---|---|
| `env` | 次回使用可能な環境 ID |
| `messages[].severity` | `info` / `warning` / `error` |
| `messages[].data` | `#eval` 出力やエラー文字列 |
| `sorries[].goal` | sorry のゴール文字列 |
| `sorries[].proofState` | tactic mode に移行する証明状態 ID |
| `goals` | tactic mode でのゴール一覧（`[]`=証明完了） |

## JSONL 入力パターン

> ⚠️ **各コマンドは空行（blank line）で区切ること。** 区切りなしで連続させると REPL が複数コマンドを 1 つの JSON として解釈し、パースエラーになる。

スクリプトが `import S2IL + Mathlib.Tactic` を自動プレペンドするため、JSONL の最初のコマンドは `"env": 0` で直接 S2IL の型・Mathlib タクティクを使える。

### 反例チェック / #eval

```jsonl
{"cmd": "#eval ([Color.red, Color.green] : List Color).map toString", "env": 0}
```

▶ stdout 例（1コマンド1行）:

```
{"env":0}
{"messages":[{"severity":"info","data":"[\"r\", \"g\"]"}],"env":1}
```

### sorry ゴール確認 → タクティク探索

```jsonl
{"cmd": "theorem foo (n : Nat) : n + 0 = n := by sorry", "env": 0}
```

▶ stdout 例（`sorries[0].goal` でゴール確認）:

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

- **env: 0 は自動プレペンドされた import の環境**: `import S2IL + Mathlib.Tactic` が env: 0。以降のコマンドは `"env": 0` で指定する
- **`S2IL` は名前空間ではない**: `import S2IL` 後は `Color`, `Direction` 等がグローバル参照可能。`open S2IL in` は不要（エラーになる）
- **起動時間**: 初回起動時 ~11-20 秒（Mathlib .olean のキャッシュ読み込み）。既にキャッシュされた環境では短縮される
- **REPL クラッシュ**: 未処理コマンド数と共にクラッシュ JSON を出力。終了コード 2
- **`unpickleEnvFrom` を JSONL に含める場合**: スクリプトが先に import を挿入するため unpickle 環境は env: 1 になる。通常は不要
