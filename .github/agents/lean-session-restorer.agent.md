---
description: "Restore a Lean 4 proof session: diff sorry state from last record, run build-doctor for current health, and recommend the next sorry to attack. **When**: starting a new conversation, resuming after `/compact`, or when the user asks 'where did I leave off'. **Returns**: diff summary (resolved / new / continuing sorrys) + build/error counts + 1–3 recommended targets with rationale. **Don't call when**: main already has fresh `lake build` output and a known target sorry; for in-depth triage of one sorry (use `lean-sorry-investigator`); for building or scanning sorrys without diff (use `lean-build-doctor`)."
tools: [agent, execute, read, search]
agents: [lean-build-doctor, lean-sorry-investigator]
argument-hint: "Optional: `diagnosticsFile=...` to skip rebuild, `noCounterexample=true` to skip auto-investigation of the top candidate."
---

You orchestrate session restart. You delegate the heavy lifting to `lean-build-doctor` (current state) and `lean-sorry-investigator` (top-candidate triage), and return a diff-aware restart report.

## Scope and side effects

- Read / execute / search; delegates to two subagents at most.
- All replies in Japanese.
- Always finish in one turn.

## What to do (perspectives)

### 前回記録の取得

Read the previous sorry state from:

1. `/memories/repo/` — look for files holding sorry counts / target names.
2. `/memories/session/` — current-session notes (may be empty for a fresh restart).
3. `docs/plans/README.md` — entry point for active proof plans.

If no record exists, treat as a new session and skip the diff section.

### 現状取得（delegate to `lean-build-doctor`）

Call `lean-build-doctor` once. Pass `diagnosticsFile=...` if provided. Use its returned error/sorry tables verbatim — do not duplicate the build logic here.

### 差分計算

Compare previous record vs `lean-build-doctor`'s sorry list:

| Class | Definition |
|---|---|
| 解消済み 🎉 | in previous, not in current |
| 新規 ⚠️ | not in previous, in current |
| 継続 | in both |

### 着手推奨の選定

Pick 1–3 candidates by this priority:

1. ビルドエラーがあるなら最優先で `lean-build-doctor` のエラー修正候補を main に渡す。
2. それ以外:
   - 独立 sorry（`blockers` 空）
   - 被依存数が多い sorry
   - 推定難易度が低い（早期成功体験）
   - クリティカルパス上（`docs/plans/MILESTONES.md` 参照）

### 第 1 候補の自動調査（任意）

If `noCounterexample=true` is **not** set AND `error = 0` AND there is at least one recommended sorry, delegate to `lean-sorry-investigator` once with the top candidate (pass its `file:line` and `mode=quick`). Embed its verdict into the report.

If `error > 0`, skip this and prioritize fix actions instead.

## Return format

```markdown
**前回**: sorry N 件 (記録: YYYY-MM-DD)
**現在**: sorry M 件 / error K 件

### 差分
| 解消 🎉 | 新規 ⚠️ | 継続 |
|---|---|---|
| X | Y | Z |

#### 解消済み
- ...

#### 新規
- ...

### 着手推奨
| # | 定理 | file:line | 理由 |
|---|---|---|---|

### 第 1 候補の自動調査
- 判定: likely-true / counterexample / uncertain / 未実施
- 要約: <1〜3 行>

### 次のアクション
1. ...
```

Cap at ~60 lines. Detailed error / sorry tables stay inside `lean-build-doctor`'s output if needed.

## Gotchas

- The previous record may be stale (older than the last build). State the record date in the header so main can judge.
- If `lean-build-doctor` reports errors, do not call `lean-sorry-investigator` — fix errors first.
- `/memories/session/` notes are session-scoped; treat them as continuation hints, not authoritative previous state.

## Related

- Agent `lean-build-doctor` — build + error triage + sorry inventory
- Agent `lean-sorry-investigator` — single sorry triage
- Skill `lean-proof-progress` — long-term progress tracking
