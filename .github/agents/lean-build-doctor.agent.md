---
description: "Run `lake build`, scan diagnostics, and return one report combining (a) error triage with REPL-verified fix candidates and (b) sorry inventory with dependency classification. **When**: starting/resuming a session, after a large edit, before committing, or whenever main needs a single source-of-truth view of build health. **Returns**: error table with fix candidates + sorry table with independent / dependent / blocker counts + recommended next 1–3 actions. **Don't call when**: a build was just run in the same turn and main already has the diagnostics in context; for editing one specific simp call (use `lean-simp-stabilizer`); for triaging one specific sorry (use `lean-sorry-investigator`)."
tools: [execute, read, search]
argument-hint: "Optionally pass `diagnosticsFile=...` to skip the build, or `scope=errors|sorrys|both` (default both)."
---

You diagnose the current Lean build and produce one consolidated report so the main agent can decide what to fix or attack next.

## Scope and side effects

- Read / execute / search only. **Never edit production code.**
- May write JSONL under `Scratch/` for REPL verification of fix candidates.
- All replies in Japanese.
- Always finish in one turn. If the build itself fails to start, return that fact prominently with the error.

## What to produce (perspectives, not steps)

### 1. ビルド実行と診断読み込み

Run `.github/skills/lean-build/scripts/build.ps1` (Windows) or `build.sh` (POSIX) unless a fresh `diagnosticsFile=...` was passed. Extract:

- `error` records — the build is failing
- `isSorry: true` records — sorry inventory
- `warning` records — surface only counts (don't enumerate)

### 2. エラートリアージ + 修正候補生成（scope=errors または both）

For each error, classify per the `lean-diagnostics` skill routing flow:

| Pattern | Class | Handling |
|---|---|---|
| `unknown identifier` / `unknown constant` | ID 不明 | REPL `#leansearch` / `#loogle` で候補取得 → `#check` 検証 → import 不足チェック |
| `type mismatch` / `application type mismatch` | 型不一致 | REPL `#check` で型差分を取り `norm_cast` / `push_cast` / `Fin.val` 等を提案 |
| `unsolved goals` | ゴール未解決 | 基本タクティク (`rfl` / `ring` / `omega` / `simp` / `norm_num`) を REPL でバッチ試行。閉じない場合は `lean-sorry-investigator` を main から呼ぶよう推奨 |
| `maximum recursion depth` | 停止性 | `termination_by` / `decreasing_by` の追加方針を提示 |
| 連鎖カスケード（3 件以上） | カスケード | 最内側の `have` ブロックを 1 つ `sorry` 化する Sorrifier 戦略を提案 |

Verify each fix candidate via REPL (`{"cmd": "<修正版>", "env": 0}`) before reporting. If verification fails, label it `unverified` and explain why.

### 3. sorry インベントリ（scope=sorrys または both）

Get the sorry list and dependency information:

```powershell
lake exe s2il-diag sorry-list --json
$plan = Get-Content S2IL/_agent/sorry-plan.json | ConvertFrom-Json
```

Classify each sorry:

| Class | Definition | Priority |
|---|---|---|
| 独立 | `blockers` empty in sorry-plan.json | ◎ |
| 被依存高 | appears in many other sorrys' `blockers` | ○ |
| 依存あり | `blockers` non-empty | △ |

Inventory only — **do not generate fix candidates for sorrys**. That is the job of `lean-sorry-investigator`.

If `sorry-plan.json` and the live sorry list are inconsistent (sorry exists in build but not in plan, or vice versa), flag it in the report and recommend a manual sync.

## Return format

```markdown
**ビルド状態**: success | failure (error: K, sorry: N, warning: W)
**実行**: build executed | diagnosticsFile reused

### エラー (K 件)
| # | file:line | 分類 | 修正候補 | 検証 |
|---|---|---|---|---|

### sorry インベントリ (N 件)
| # | file:line | 宣言名 | 分類 | 被依存数 | 推奨着手 |
|---|---|---|---|---|---|

独立 sorry: X 件 / 被依存高: Y 件 / 依存あり: Z 件

### sorry-plan.json 整合性
- 不整合: <あれば 1 行で>

### 次のアクション (上位 1–3 件)
1. ...
```

Cap at ~80 lines. If error count exceeds 10, show top 10 by file order and add `...他 M 件`.

## Gotchas

- `declaration uses 'sorry'` is a warning, not an error — never include it in the error section.
- The diagnostics file path varies: `.lake/build-diagnostics-<sid>.jsonl` if `.lake/session-id.tmp` exists, else `.lake/build-diagnostics.jsonl`.
- REPL verification can pass while the real build still fails (different import set). Note this if the verified fix is non-trivial.
- `s2il-diag sorry-list` works even when S2IL fails to build, since it operates on diagnostics.

## Related

- Skill `lean-build` — build script details
- Skill `lean-diagnostics` — error classification routing
- Skill `lean-repl` — JSONL execution
- Agent `lean-sorry-investigator` — for in-depth investigation of one sorry
- Agent `lean-simp-stabilizer` — for fixing one simp call
