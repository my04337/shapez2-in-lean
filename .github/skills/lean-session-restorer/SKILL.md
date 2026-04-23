---
name: lean-session-restorer
description: >
  Automate Lean 4 proof session restart: diff sorrys, recommend next sorry.
  Use when: resume proof session, session restore, continue proof work,
  what to work on next, session start, proof session resume, pick up where I left off.
metadata:
  argument-hint: 'Omit to auto-restore current session'
---

# セッション復元スキル

前回セッションの状態を復元し、今回着手すべき sorry を推奨する。
sorry スナップショット取得は **lean-sorry-snapshot** エージェントに、
個別エラーの修正は **lean-error-fixer** エージェントに委ねる。

> **lean-proof-progress** スキルとの違い**: lean-proof-progress は撤退判断・長期トラッキングの**指針**を提供する。
> このスキルは**セッション開始時の状態復元フロー**を具体的な手順として提供する。

---

## Step 1: 前回の記録を読む

以下の場所から前回セッションの情報を収集する:

| 情報源 | 読む内容 |
|---|---|
| `/memories/repo/` | sorry 状態の記録（前回セッション終了時のスナップショット） |
| `/memories/session/` | 現セッションのメモ（存在する場合） |
| `docs/plans/README.md` | 証明計画の入口。現在のタスクに対応する個別計画が必要か確認する |

前回の sorry 数と対象の定理名リストを記録する。

---

## Step 2: 現在の sorry 状態を取得

**lean-sorry-snapshot** エージェント相当のビルド → sorry 抽出を実行する。

**Windows:**
```powershell
.github/skills/lean-build/scripts/build.ps1

$sid = if (Test-Path .lake/session-id.tmp) { (Get-Content .lake/session-id.tmp -Raw).Trim() } else { $null }
$diagFile = if ($sid -and (Test-Path ".lake/build-diagnostics-$sid.jsonl")) { ".lake/build-diagnostics-$sid.jsonl" } else { ".lake/build-diagnostics.jsonl" }

# sorry 一覧
$sorries = Get-Content $diagFile | ConvertFrom-Json | Where-Object { $_.isSorry -eq $true }
$sorries | Select-Object file, line, message | Format-Table -AutoSize

# error 一覧
$errors = Get-Content $diagFile | ConvertFrom-Json | Where-Object { $_.severity -eq "error" }
$errors | Select-Object file, line, message | Format-Table -AutoSize
```

**macOS / Linux:**
```bash
.github/skills/lean-build/scripts/build.sh

SID=$(cat .lake/session-id.tmp 2>/dev/null | tr -d '[:space:]')
DIAG_FILE=".lake/build-diagnostics.jsonl"
[ -n "$SID" ] && [ -f ".lake/build-diagnostics-$SID.jsonl" ] && DIAG_FILE=".lake/build-diagnostics-$SID.jsonl"

# sorry 一覧
grep '"isSorry":true' "$DIAG_FILE" | jq '{file, line, message}'

# error 一覧
grep '"severity":"error"' "$DIAG_FILE" | jq '{file, line, message}'
```

---

## Step 3: 差分分析

Step 1 の前回記録と Step 2 の現在の状態を比較する。

| 分析項目 | 内容 |
|---|---|
| 解消済み sorry | 前回あって今回ない sorry（進捗） |
| 新規 sorry | 前回なくて今回ある sorry（退行） |
| 継続 sorry | 前回も今回もある sorry |
| ビルドエラー | error が存在する場合、修正が先決 |

---

## Step 4: 着手推奨の決定

以下の優先順で着手すべき sorry を推奨する（**lean-proof-progress** スキルの優先順位に準拠）:

1. **独立 sorry**: 他に依存しない → 即着手可能
2. **被依存数が多い**: 解決のインパクトが大きい
3. **推定難易度が低い**: 早期の成功体験
4. **クリティカルパス上**: プロジェクト目標に直結

ビルドエラーがある場合は sorry より先にエラー修正を推奨する。

---

## 出力フォーマット

### セッション復元レポート

**前回の状態**: sorry N 件（`/memories/repo/` 記録: YYYY-MM-DD）
**現在の状態**: sorry M 件、error K 件

#### 差分

| 項目 | 数 | 詳細 |
|---|---|---|
| 解消済み sorry | X | `bar_lemma` (S2IL/Foo.lean:42) 等 |
| 新規 sorry | Y | `new_thm` (S2IL/Bar.lean:10) 等 |
| 継続 sorry | Z | `qux_thm` (S2IL/Baz.lean:55) 等 |
| ビルドエラー | K | → **lean-error-fixer** で修正推奨 |

#### 着手推奨

| # | 定理名 | ファイル:行 | 理由 |
|---|---|---|---|
| 1 | `independent_lemma` | `S2IL/Baz.lean:55` | 独立 sorry・被依存数 3 |
| 2 | `chain_start` | `S2IL/Qux.lean:20` | クリティカルパス上 |

### 前回記録なしの場合

前回の sorry 記録が `/memories/repo/` に存在しない場合は、差分分析をスキップし、
現在の sorry スナップショットのみ提示する。

---

## Gotchas

- `/memories/repo/` に前回記録がない場合（初回セッション等）は差分分析をスキップする
- ビルドエラーがある場合は sorry 分析の前にエラー修正を優先する
- `docs/plans/` 内の個別計画は流動的な場合がある。README を入口にし、必要な個別資料だけを参照する
- 計画資料の記述とビルド結果が食い違う場合は、ビルド結果を信頼源とする

## 関連

- **スキル**: `lean-proof-progress`（撤退判断・長期トラッキングの指針）
- **スキル**: `lean-build`（ビルドスクリプトの詳細）
- **エージェント**: `lean-sorry-snapshot`（sorry 一覧 + 依存グラフの一括取得）
- **エージェント**: `lean-error-fixer`（ビルドエラーの自動修正）
