---
name: lean-tooling
description: >
  Reference hub for S2IL Lean execution tooling: build.ps1 diagnostics, persistent REPL JSONL, run.ps1, setup PATH, and Windows terminal safety. Use when: build lean project, lake build, compile Lean, REPL, #eval, run Lean file, lake exe, PATH setup, toolchain, ビルド, REPL, 実行, ツールチェイン. Returns: canonical command entrypoints + mode selection + links to detailed references. Don't call when: you need build error triage (use agent `lean-build-doctor`) or theorem investigation (use agent `lean-theorem-investigator`).
---

# Lean Tooling

Lean の実行系入口を 1 箇所に集約する active skill。詳細な旧 skill 本文は `references/` に移し、実行スクリプトは `scripts/` に集約する。

## 標準入口

| 目的 | コマンド |
|---|---|
| 既定ビルド | `.github/skills/lean-tooling/scripts/build.ps1` |
| 局所ビルド | `.github/skills/lean-tooling/scripts/build.ps1 -Target <module>` |
| Test ライブラリ | `.github/skills/lean-tooling/scripts/build.ps1 -Target Test` |
| REPL JSONL 送信 | `.github/skills/lean-tooling/scripts/repl.ps1 -Send -SessionId <id> -CmdFile <file>` |
| 一時 `.lean` 実行 | `.github/skills/lean-tooling/scripts/run-lean-file.ps1 -File Scratch/<file>.lean` |
| `lake exe` 実行 | `.github/skills/lean-tooling/scripts/run.ps1 -Target <exe>` |
| PATH セットアップ確認 | `.github/skills/lean-tooling/scripts/setup.ps1` |

## 判断フロー

| 状況 | 使う入口 |
|---|---|
| コミット前・大きな編集後の正本確認 | `lean-build-doctor mode=verify-only` または build script |
| Lean エラー分類や修正候補が必要 | `lean-build-doctor` |
| tactic / `#check` / `#eval` を軽く試す | REPL JSONL |
| Scratch の計算ハーネスを安全に走らせる | `run-lean-file.ps1` |
| 実行可能ターゲットの出力を確認 | `run.ps1` |
| `lean` / `lake` が見つからない | `setup.ps1` |

## Windows terminal safety

PowerShell here-string (`@' ... '@`, `@" ... "@`) や `lake env lean --stdin` パイプを `run_in_terminal` に直接渡さない。継続入力 `>>` が残ると後続コマンドが混線する。

推奨パターン:

```powershell
$path = "Scratch/check-<unique>.lean"
Set-Content -LiteralPath $path -Encoding UTF8 -Value @('import S2IL', '#check Nat')
.github/skills/lean-tooling/scripts/run-lean-file.ps1 -File $path
```

探索的 `#eval` / Plausible / ベンチマークは小さく始め、有限 timeout を付ける。通常ビルドは `.github/skills/lean-tooling/scripts/build.ps1` を正本にする。

## 詳細参照

| 参照 | 役割 |
|---|---|
| [`references/build.md`](references/build.md) | build script と diagnostics JSONL の詳細 |
| [`references/repl.md`](references/repl.md) | Persistent REPL / JSONL / `run-lean-file.ps1` |
| [`references/run.md`](references/run.md) | `lake exe` 実行 wrapper |
| [`references/setup.md`](references/setup.md) | elan / lake / lean PATH 解決 |
