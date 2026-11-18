import HexagonCover.E4InsideCentral

/-! Same-pose area bounds needed to derive the T2/T3 direction windows. -/
namespace HexagonCover.E4InsideArea
noncomputable section
open HexagonCover.Configuration NormalizedHeavy

theorem expanded_area {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) :
    (M h)^2+((a h.cover 0)^2+((a h.cover 1)^2+((a h.cover 2)^2+
      ((a h.cover 3)^2+(a h.cover 4)^2)))) ≤ 1 := by
  have hh := SoleGapArea.actual_area_window h sole
  simpa [Fin.sum_univ_succ] using hh

theorem a2_lt_twenty_three {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) : a h.cover 2 < 23/100 := by
  have hM := GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩
  have harea := expanded_area h sole
  have hmono := (SoleGapArea.a_strictMono h sole).monotone
  have h23 := hmono (show (2:Fin 5) ≤ 3 by decide)
  have h24 := hmono (show (2:Fin 5) ≤ 4 by decide)
  change a h.cover 2 ≤ a h.cover 3 at h23
  change a h.cover 2 ≤ a h.cover 4 at h24
  have hs23 := pow_le_pow_left₀ (leftReach h.cover 2).positive.le h23 2
  have hs24 := pow_le_pow_left₀ (leftReach h.cover 2).positive.le h24 2
  by_contra hn
  have hl : 23/100 ≤ a h.cover 2 := le_of_not_gt hn
  nlinarith [sq_nonneg (a h.cover 0),sq_nonneg (a h.cover 1)]

theorem a3_lt_third {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) : a h.cover 3 < 1/3 := by
  have hM := GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩
  have harea := expanded_area h sole
  have hmono := (SoleGapArea.a_strictMono h sole).monotone
  have h34 := hmono (show (3:Fin 5) ≤ 4 by decide)
  change a h.cover 3 ≤ a h.cover 4 at h34
  have hs34 := pow_le_pow_left₀ (leftReach h.cover 3).positive.le h34 2
  by_contra hn
  have hl : 1/3 ≤ a h.cover 3 := le_of_not_gt hn
  nlinarith [sq_nonneg (a h.cover 0),sq_nonneg (a h.cover 1),sq_nonneg (a h.cover 2)]

#print axioms a2_lt_twenty_three
#print axioms a3_lt_third

end
end HexagonCover.E4InsideArea
