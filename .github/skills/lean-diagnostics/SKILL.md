---
name: lean-diagnostics
description: 'Parse and triage Lean 4 build diagnostics. Use when: analyze build errors, triage warnings, prioritize fixes, parse diagnostics, review build output, sorry detection.'
metadata:
  argument-hint: 'Pass build output or diagnostics file path'
---

# ビルド診断スキル

**lean-build** の出力を解析し、修正すべき問題を優先順位付けする。

## クイックリファレンス

```powershell
.github/skills/lean-build/scripts/build.ps1

$diags = Get-Content .lake/build-diagnostics.jsonl | ConvertFrom-Json
$diags | Where-Object { $_.severity -eq "error" }                    # 修正必須
$diags | Where-Object { $_.isSorry -eq $true }                       # 証明未完了
$diags | Where-Object { $_.severity -eq "warning" -and !$_.isSorry } # 非sorry warning
```

## 状態判断フロー

```
ビルド実行 → "status: success" か?
  ├─ No  → errors を修正
  └─ Yes → 非sorry warning あり? → 修正（Stop Hook がブロック）
              └─ sorry のみ      → 証明作業へ
```

## トリアージ優先順位

| 優先度 | レベル | 対応 |
|---|---|---|
| 1 | **error** | ビルドを阻害。必ず修正 |
| 2 | **sorry** | 未証明定理。`isSorry: true` で自動識別 |
| 3 | **warning** | 未使用変数・非推奨 API 等 |
| 4 | **info** | 情報。通常対応不要 |

## エラー種別 → 対応スキル/ツール ルーティング

ビルドエラーの種別に応じて、最適なスキル・ツールを自動選択する。

### error レベル

| エラーメッセージパターン | 第1候補 | 第2候補 | 備考 |
|---|---|---|---|
| `unknown identifier '...'` | `lean-mathlib-search` スキル → `#loogle` / `#leansearch` | REPL `exact?` | Mathlib/Batteries の名前変更・移動が原因のことが多い |
| `unknown constant '...'` | `grep_search` で定義箇所を検索 | `import` 追加 | ファイル内定義の参照漏れ or import 不足 |
| `type mismatch` | REPL でゴール型を確認 → `norm_cast` / `push_cast` | `lean-tactic-select` スキル | 型変換（Nat↔Int, Fin↔Nat 等）が原因 |
| `unsolved goals` | `lean-goal-advisor` エージェント | `lean-tactic-select` スキル | ゴール形状を分析して適切なタクティクを選択 |
| `application type mismatch` | 引数の型を REPL `#check` で確認 | `@` で明示適用 | 暗黙引数の推論失敗が多い |
| `function expected` | 括弧・適用の構文を確認 | — | 通常は構文ミス |
| `declaration uses 'sorry'` | `lean-proof-planning` スキル | — | sorry 解消の計画を立てる |
| `maximum recursion depth` | `decreasing_by` / `termination_by` を追加 | `WellFoundedRelation` を確認 | 停止性証明が必要 |
| 複数エラーが連鎖 | **Sorrifier パターン**: 最内側から 1 箇所ずつ sorry 化→再ビルド | — | カスケードエラーの除去を優先 |

### warning レベル（actionable）

| warning パターン | 対応 |
|---|---|
| `unused variable` | `_x` にリネーム or 削除 |
| `This simp argument is unused` | `lean-simp-stabilizer` エージェント or 手動で `simp only [...]` から削除 |
| `this tactic is never executed` | tactic を削除 |
| `simp made no progress` | 条件を確認し `simp` を適切なタクティクに変更 |

### ルーティング判断フロー

> **自動修正**: error が複数ある場合は **lean-error-fixer** エージェントに委譲すると、
> 分類→修正候補生成→REPL検証を自動実行できる。

```
エラーメッセージを取得
  ├─ 複数 error → lean-error-fixer エージェントに一括委譲（推奨）
  ├─ `unknown identifier` / `unknown constant` → 補題検索（lean-mathlib-search）
  ├─ `type mismatch` / `application type mismatch` → 型分析（REPL #check）
  ├─ `unsolved goals` → ゴール分析（lean-goal-advisor）
  ├─ `sorry` → 証明計画（lean-proof-planning）
  ├─ 複数エラー連鎖 → Sorrifier パターン（最内側優先 sorry 化）
  └─ その他 → メッセージを読んで手動判断
```

## タスク完了前の必須確認

`.lean` ファイル変更後は非sorry warning を整理すること。Stop Hook が自動ブロックする。

```powershell
# 非sorry warning をリストアップ
Get-Content .lake/build-diagnostics.jsonl | ConvertFrom-Json |
    Where-Object { $_.severity -eq "warning" -and !$_.isSorry } |
    Select-Object file, line, message
```

> actionable warning の詳細は上記「エラー種別 → 対応スキル/ツール ルーティング」の warning レベルを参照。

### Stop Hook の動作

- 非sorry warning あり → `decision: "block"` で終了を阻止
- sorry のみ → `continue: true` で通過（進捗記録を促す）
- `stop_hook_active: true`（再入）→ 無条件通過（無限ループ防止）

## sorry の依存関係分析

`lean-sorry-snapshot` エージェントでビルド→sorry 抽出→depgraph→依存分類を一括実行可能。
詳細な sorry 分類（独立/依存/被依存）と依存グラフの取得は `lean-sorry-snapshot` エージェントに委ねる。

## 関連スキル

**lean-build** / **lean-depgraph** / **lean-proof-progress** / **lean-error-fixer**（エラー自動修正スキル）

エージェント: **lean-error-fixer**（本スキルのルーティングを自動実行するエージェント） / **lean-sorry-snapshot**（sorry 一覧 + 依存グラフ）
