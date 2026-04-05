-- Pattern 4 redo
example (a : α) (as : List α) : (a :: as).length ≥ 1 := by simp? [List.length]

-- Pattern 10 redo
example (c : Bool) : !(false || c) = !c := by simp?

-- Pattern 12 redo
example [BEq α] [LawfulBEq α] (pos : α) : !(pos == pos) = false := by simp? [BEq.rfl]

-- Pattern 13 redo
example (a : α) (as : List α) (l : List α) (hf : l = a :: as) (h : l.length = 0) : False := by simp? [hf] at h
