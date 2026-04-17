# Scratch/ — 一時ファイル・実験作業

> このファイルは `Scratch/` 配下のファイル（`.lean`・`.jsonl`）編集時に自動適用される（`chat.useNestedAgentsMdFiles` 有効時）。
> プロジェクト全体の規約は [AGENTS.md](../AGENTS.md)、Lean 証明コードの規約は [S2IL/AGENTS.md](../S2IL/AGENTS.md) を参照。

## このディレクトリの用途

`Scratch/` は**実験・検証用の一時的なファイル置き場**であり、`*.lean` と `*.jsonl` は `.gitignore` 対象。

| 種類 | 用途 | 命名規則 |
|---|---|---|
| `*.lean` | Lean 式・定理の型チェック / `#eval` | `UpperCamelCase`（例: `GravityCheck.lean`） |
| `*.jsonl` | REPL コマンドバッチ | `commands-<sessionId>.jsonl`（不明時: `commands.jsonl`） |
| `commands.jsonl` | セッション ID 不明時のフォールバック | 固定名 |

## ディレクトリ別の役割分担

```
Scratch/        ← エージェントが作成する一時 Lean / JSONL ファイルはここ
.repl/<session>/ ← REPL デーモンのインフラファイル（エージェントは直接作成しない）
                   _session-in.jsonl, _session-out.jsonl, daemon.pid, ready 等
```

**`.repl/` への Lean ファイル・JSONL コマンドファイルの作成は禁止。** `.repl/` は REPL スクリプトが管理するインフラ用ディレクトリ。

## 実行方法

```powershell
# 型チェック / #eval
lake env lean Scratch/MyFile.lean

# def main の実行（--run は必ずファイル名より前に置く）
lake env lean --run Scratch/MyFile.lean
```

## Lean ファイルの使い分け

- **数行の即時確認**: REPL を優先（`lean-repl` スキル参照）
- **複数定義・10 行以上**: `Scratch/*.lean` を使う
- **証明骨格・仮説メモ**: Markdown（`/memories/session/` 等）に書く

## JSONL ファイルの生成規則

### 生成方法（`run_in_terminal` + `Set-Content`）

```powershell
# ✅ 正しい生成方法
'{"cmd": "#eval 1+1", "env": 0}' | Set-Content Scratch/commands.jsonl

# ✅ 複数行（ヒアストリング）
@'
{"cmd": "#eval 1+1", "env": 0}

{"cmd": "theorem test : 1 + 1 = 2 := by norm_num", "env": 0}
'@ | Set-Content Scratch/commands.jsonl
```

```powershell
# ❌ create_file で JSONL 生成（\n が実際の改行に展開されて JSON 破損）
```

### ファイル命名ルール

- 同一探索テーマ内の繰り返しテストは**同一ファイルに追記**する（連番ファイルを増殖させない）
- 新ファイルを作るのは別テーマの場合のみ
- 1 セッション内の REPL ファイル作成は**最大 3 件まで**

```
✅ 同じテーマで修正 → commands.jsonl を上書き再利用
❌ commands-check2.jsonl, commands-check3.jsonl と連番で増殖
```

## Unicode 文字を含む Lean コード

`∀`、`¬`、`≤`、`⊢` 等の Unicode 文字は REPL の Persistent モードおよびバッチ JSONL 内でそのまま使用できる。

ただし JSONL へのエスケープが複雑になる場合（多数の Unicode を含む長い証明等）は `Scratch/*.lean` に直接記述して `lake env lean Scratch/File.lean` で評価する方が確実。

## Scratch/commands.jsonl の読み取り前確認

この JSONL ファイルは**前セッションの内容が残っている可能性がある**。`replace_string_in_file` や `create_file` を使う前に必ず `read_file` で現在の内容を確認すること。
