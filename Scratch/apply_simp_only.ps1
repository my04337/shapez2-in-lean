# Apply all simp → simp only replacements to CrystalBond.lean
$file = "S2IL/Behavior/CrystalBond.lean"
$lines = Get-Content $file

# Line numbers are 1-indexed, array is 0-indexed
# Each entry: [line_number, old_pattern, new_text]
# Use exact substring match on the line

function Replace-Line($lineNum, $old, $new) {
    $idx = $lineNum - 1
    $line = $lines[$idx]
    if ($line.Contains($old)) {
        $lines[$idx] = $line.Replace($old, $new)
        Write-Output "OK L${lineNum}: $old -> $new"
    } else {
        Write-Output "FAIL L${lineNum}: '$old' not found in: $($line.Trim())"
    }
}

# 1. L181
Replace-Line 181 'simp [Shape.rotate180, Shape.mapLayers]' 'simp only [Shape.rotate180, Shape.mapLayers]'

# 2. L190
Replace-Line 190 'simp [getDir_rotate180]' 'simp only [Option.map_some, getDir_rotate180]'

# 3. L228
Replace-Line 228 'simp [QuarterPos.rotate180, dir_beq_rotate180'']' 'simp only [QuarterPos.rotate180, dir_beq_rotate180'']'

# 4. L277
Replace-Line 277 'simp [bfs]' 'simp only [bfs, List.map_nil]'

# 5. L302
Replace-Line 302 'simp [Shape.layerCount_rotate180]' 'simp only [Shape.layerCount_rotate180]'

# 6. L358
Replace-Line 358 'simp [h_vis]' 'simp only [h_vis, Bool.or_true]'

# 7. L370
Replace-Line 370 'simp [BEq.rfl]' 'simp only [BEq.rfl, List.any_nil, Bool.or_false]'

# 8. L392
Replace-Line 392 'simp [h_q]' 'simp only [h_q, Bool.or_true]'

# 9. L401
Replace-Line 401 'simp [BEq.rfl]' 'simp only [BEq.rfl, Bool.true_or]'

# 10. L410
Replace-Line 410 'simp [h_rest]' 'simp only [h_rest, Bool.or_true]'

# 11. L417
Replace-Line 417 'simp [BEq.rfl]' 'simp only [BEq.rfl, Bool.true_or]'

# 12. L460
Replace-Line 460 'simp [QuarterPos.rotate180]' 'simp only [QuarterPos.rotate180]'

# 13. L466
Replace-Line 466 'simp [QuarterPos.rotate180] at h_lt' 'simp only [QuarterPos.rotate180] at h_lt'

# 14. L467
Replace-Line 467 'simp [h])' 'simp only [h, Bool.false_eq_true, not_false_eq_true])'

# 15. L480
Replace-Line 480 'simp [QuarterPos.rotate180]' 'simp only [QuarterPos.rotate180]'

# 16. L485
Replace-Line 485 'simp [QuarterPos.rotate180_rotate180, BEq.rfl]' 'simp only [QuarterPos.rotate180_rotate180, BEq.rfl]'

# 17. L488
Replace-Line 488 'simp [h])' 'simp only [h, Bool.false_eq_true, not_false_eq_true])'

# 18. L501
Replace-Line 501 'simp at h_a_valid' 'simp only at h_a_valid'

# 19. L520
Replace-Line 520 'simp [hl] at h_m' 'simp only [hl, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at h_m'

# 20. L529
Replace-Line 529 'simp [hl] at h_m' 'simp only [hl, reduceCtorEq, imp_self, implies_true, Bool.false_eq_true] at h_m'

# 21. L545
Replace-Line 545 'simp [hl] at h_m' 'simp only [hl, Bool.false_eq_true] at h_m'

# 22. L554
Replace-Line 554 'simp [hl] at h_m' 'simp only [hl, Bool.false_eq_true] at h_m'

# 23. L592
Replace-Line 592 'simp [List.any] at hv' 'simp only [List.any, Bool.false_eq_true] at hv'

# 24. L632
Replace-Line 632 'simp [hb, h_nv]' 'simp only [hb, h_nv, Bool.not_false, Bool.and_self]'

# 25. L637
Replace-Line 637 'simp [h])' 'simp only [h, Bool.or_true])'

# 26. L641
Replace-Line 641 'simp [h_pn])' 'simp only [h_pn, Bool.true_or])'

# 27. L680
Replace-Line 680 'simp [List.filter]' 'simp only [List.filter, List.length_nil, Std.le_refl]'

# 28. L734
Replace-Line 734 'simp [List.any] at h_q' 'simp only [List.any, Bool.false_eq_true] at h_q'

# 29. L735
Replace-Line 735 'simp [List.length]' 'simp only [List.length, ge_iff_le, Nat.le_add_left]'

# 30. L752
Replace-Line 752 'simp [List.length] at h_u_zero' 'simp only [List.length, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at h_u_zero'

# 31. L763
Replace-Line 763 'simp [h_vis_x]' 'simp only [h_vis_x, Bool.not_false]'

# 32. L811
Replace-Line 811 'simp [h_pos])' 'simp only [h_pos, Bool.false_eq_true, not_false_eq_true])'

# 33. L816
Replace-Line 816 'simp [h_no_bond x]' 'simp only [h_no_bond x, List.any_cons, Bool.not_or, Bool.false_and]'

# 34. L847
Replace-Line 847 'simp [this]' 'simp only [this, Bool.false_or]'

# 35. L861
Replace-Line 861 'simp [h_vis_false]' 'simp only [h_vis_false, Bool.not_false]'

# 36. L878
Replace-Line 878 'simp [BEq.rfl])' 'simp only [BEq.rfl, Bool.not_true])'

# 37. L888
Replace-Line 888 '| zero => simp' '| zero => simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]'

# 38. L891
Replace-Line 891 'simp [List.flatMap_cons, List.flatMap_nil, List.map, Direction.all]' 'simp only [Direction.all, List.map_cons, List.map, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]'

# 39. L912
Replace-Line 912 'simp [List.any] at h' 'simp only [List.any, Bool.false_eq_true] at h'

# 40. L944
Replace-Line 944 'simp [List.any] at h_vis' 'simp only [List.any, Bool.false_eq_true] at h_vis'

# 41. L951
Replace-Line 951 'simp [List.any] at h_rest' 'simp only [List.any, Bool.false_eq_true] at h_rest'

# 42. L973
Replace-Line 973 'simp [List.any])' 'simp only [List.any, Bool.not_false])'

# 43. L1008
Replace-Line 1008 'by simp' 'by simp only [QuarterPos.rotate180_rotate180]'

# 44. L1015
Replace-Line 1015 'simp [Shape.layerCount_rotate180, allValid_rotate180_eq, h_lc, bfs] at hp' 'simp only [allValid_rotate180_eq, Shape.layerCount_rotate180, h_lc, Nat.zero_mul, Nat.mul_zero, bfs, List.any_nil, Bool.false_eq_true] at hp'

# 45. L1027
Replace-Line 1027 'simp [h_lc, bfs] at hq' 'simp only [h_lc, Nat.zero_mul, Nat.mul_zero, bfs, List.any_nil, Bool.false_eq_true] at hq'

# Write back
$lines | Set-Content $file
Write-Output ""
Write-Output "Done. All 45 replacements applied."
