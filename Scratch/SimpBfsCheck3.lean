-- Pattern 10 exact context: after cases h_eq : (pos == x) with | false =>
-- in the filter_congr closure, goal is about Bool.not_or decomposition
-- Actually, after simp only [List.any_cons], we get the ||, then cases splits
-- In false branch, the discriminant is substituted:
example [BEq α] (pos x : α) (vis : List α) (h_eq : (pos == x) = false) :
    !((pos == x) || vis.any (· == x)) = !(vis.any (· == x)) := by
    simp? [h_eq]
