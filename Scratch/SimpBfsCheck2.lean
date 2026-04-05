-- Test the exact contexts that fail in the build

-- Pattern 4 context (line 263/379): goal is (pos :: rest).length ≥ 1 after cases cons
-- NOT exactly (a :: as).length ≥ 1, it might have a different structure
-- Let me test the exact pattern:
example (pos : α) (rest : List α) : (pos :: rest).length ≥ 1 := by
    simp?

-- Pattern 12 context (line 358/504):
-- Goal is `(fun p => !(pos == p)) pos = false`
-- This might NOT beta-reduce automatically
example [BEq α] [LawfulBEq α] (pos : α) : (fun p => !(pos == p)) pos = false := by
    simp? [BEq.rfl]

-- Pattern 13 context (line 401):
-- hf is renaming a pattern from cases, h_u_zero has a specific form
-- The actual context uses `hf : ... = _ :: _` from cases
variable (q : α → Bool) (allNodes : List α) (vis : List α) [BEq α]
example (a : α) (as : List α) (hf : allNodes.filter (fun q => !(vis.any (· == q))) = a :: as)
    (h_u_zero : (allNodes.filter fun q => !(vis.any (· == q))).length = 0) : False := by
    simp? [hf] at h_u_zero
