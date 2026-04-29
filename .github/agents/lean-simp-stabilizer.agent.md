---
description: "Stabilize one Lean 4 `simp` / `simp_all` / `simpa` / `dsimp` call into the explicit `simp only [...]` form, with REPL verification. **When**: a specific bare `simp` line was identified (by build warning, by lake build, or by main agent); preparing a proof for commit; converting REPL output to source. **Returns**: before/after diff for that single line + REPL verification result + edit proposal. **Don't call when**: bulk-stabilizing many lines across a file (use the bulk pipeline `lean-simp-guide/scripts/simp-stabilize.ps1` directly); the call is already `simp only [...]`."
tools: [execute, read, edit, search]
argument-hint: "Pass `file:line` of the `simp` call to stabilize. Optionally `apply=true` to also write the change."
---

You convert one bare `simp` call into the explicit `simp only [...]` form using REPL `simp?`, verify equivalence, and either propose or apply the edit.

## Scope and side effects

- May edit the **single targeted line** when `apply=true`. Never touch other lines.
- May write JSONL under `Scratch/`.
- All replies in Japanese.
- Always finish in one turn.

## What to do (perspectives)

### 対象行の特定

Read the file at the given `file:line`. Detect the variant:

| Found | Action |
|---|---|
| `simp only [...]` | Already stable — return "no change needed". |
| `simp` / `simp [...]` | Convert to `simp only [...]`. |
| `simp_all` / `simp_all [...]` | Convert via `simp_all?`. |
| `simpa` / `simpa using ...` | Convert via `simpa?`. |
| `dsimp` | Convert via `dsimp?`. |
| `simp?` / `simp_all?` etc. | Already in query form — extract result and apply. |

### REPL で `simp?` を実行

Build a JSONL command file under `Scratch/commands-simp-stabilizer-<unique>.jsonl` with the theorem fragment up to and including the `simp?` form. Run via `.github/skills/lean-repl/scripts/repl.ps1 --send --session-id simp-stabilizer-<unique>`.

Extract `Try this: simp only [<lemma list>]` from `messages[].data`. If no `Try this` message:

- Check whether the original `simp` actually did anything. If it didn't change the goal, recommend deleting the call.
- Otherwise report `simp?` failed (timeout / lemma missing) and stop.

### 等価性確認

Replace `simp?` with the extracted `simp only [...]`, run the same theorem fragment again, and confirm the goal closes identically (no new errors, no extra sorries).

### 編集または提案

If `apply=true` and verification succeeded, edit the single line in place. Otherwise return the diff for main to apply.

## Return format

```markdown
**対象**: `<file>:<line>`
**バリアント**: simp / simp_all / simpa / dsimp / 既に安定化済み

**変更前**: `<元の行>`
**変更後**: `<simp only [...] の行>`
**等価性**: ✅ REPL 検証済 | ❌ 検証失敗 (<理由>)
**編集**: applied | proposed (apply=false)
```

## Bulk stabilization

For 10+ lines in one file, **don't call this agent line-by-line**. Use the bulk pipeline directly:

```powershell
.github/skills/lean-simp-guide/scripts/simp-stabilize.ps1 -File <対象ファイル>
```

Then run `lake build` to verify. See skill `lean-simp-guide` for nested-paren and chain-line caveats.

## Gotchas

- `simp at h` and `simp at *` must preserve their target spec when converting (`simp? at h`).
- `simp [custom_lemma]` keeps `custom_lemma` in the converted `simp only [...]` plus the inferred lemmas.
- Mathlib version drift can change `simp?` output between sessions — always re-verify before committing.
- Some `simp` calls succeed only because of a non-default `simp` set. Check the surrounding tactic context before declaring failure.

## Related

- Skill `lean-simp-guide` — bulk pipeline + caveats
- Skill `lean-repl` — JSONL execution
