---
name: lean-diagnostics
description: 'Lean 4 ビルド・実行結果の診断メッセージを解析・トリアージする。Use when: analyze build errors, triage warnings, prioritize fixes, parse diagnostics, review build output, sorry detection.'
metadata:
  argument-hint: 'ビルド結果の診断とトリアージを行います'
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

## タスク完了前の必須確認

`.lean` ファイル変更後は非sorry warning を整理すること。Stop Hook が自動ブロックする。

```powershell
# 非sorry warning をリストアップ
Get-Content .lake/build-diagnostics.jsonl | ConvertFrom-Json |
    Where-Object { $_.severity -eq "warning" -and !$_.isSorry } |
    Select-Object file, line, message
```

### 代表的な actionable warning

| warning | 修正 |
|---|---|
| `unused variable` | `_x` にリネームまたは削除 |
| `This simp argument is unused` | `simp only [...]` から削除 |
| `this tactic is never executed` | tactic を削除 |

### Stop Hook の動作

- 非sorry warning あり → `decision: "block"` で終了を阻止
- sorry のみ → `continue: true` で通過（進捗記録を促す）
- `stop_hook_active: true`（再入）→ 無条件通過（無限ループ防止）

## sorry の依存関係分析

`lean-sorry-snapshot` サブエージェントでビルド→sorry 抽出→depgraph→依存分類を一括実行可能。

## 関連スキル

**lean-build** / **lean-depgraph** / **lean-proof-progress**
> ビルド・sorry 抽出・depgraph 生成・依存分類をすべて実行し、構造化された sorry テーブルが返される。
> 手動で次の手順を実行する必要がなくなる。

### sorry 依存グラフの取得

**lean-depgraph** を使って sorry を含む宣言の依存関係を可視化する:

```powershell
.github/skills/lean-depgraph/scripts/depgraph.ps1 -SorryOnly -Json
```

sorry ノードのみ抽出した依存グラフが `.lake/depgraph.json` に生成される。  
`lean-sorry-snapshot` サブエージェントでビルド→sorry 抽出→depgraph を一括実行できる。
.github/skills/lean-depgraph/scripts/depgraph.ps1
```

### sorry の分類

| 分類 | 意味 | 対応方針 |
|---|---|---|
| **独立 sorry** | 他の sorry に依存しない | 即座に着手可能。優先候補 |
| **依存 sorry** | 他の sorry の結果を前提とする | 依存先を先に解決 |
| **被依存 sorry** | 多くの宣言がこの sorry に依存 | 解決のインパクトが大きい |

### sorry の型シグネチャ要約

sorry の対象（何を証明する必要があるか）を素早く把握するには:

```powershell
# Windows: sorry を含む宣言の一覧
Get-Content .lake/build-diagnostics.jsonl |
    ConvertFrom-Json |
    Where-Object { $_.isSorry -eq $true } |
    Select-Object file, line, message
```

```bash
# macOS / Linux
grep '"isSorry":true' .lake/build-diagnostics.jsonl | jq '{file, line, message}'
```

sorry の行番号から対象の `theorem` / `lemma` 宣言を特定し、
その型シグネチャ（ゴール）を確認する。
