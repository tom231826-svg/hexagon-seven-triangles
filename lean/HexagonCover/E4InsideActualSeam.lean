import HexagonCover.E4InsideSeamGeometry
import HexagonCover.E4InsideOwners
import HexagonCover.E4T3Actual

/-! Full actual T1/T2/T3 owner contradiction. Every reach, duty point and
chart comes from the same normalized seven-piece placement. Source-exposed
simplifications: La closes nonnegative r directly; a monotone quadratic lower
envelope closes the large-s negative case without calculus. The actual Qt
first row itself supplies the T1 negative-slope window, so this closure does
not require the separate fixed-Z packet. -/
namespace HexagonCover.E4InsideActualSeam
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
open E4InsideRayChart E4InsideActualChart E4InsideSeamGeometry E4InsideSeamScalar
local notation "h₀" => NICertificate.halfRoot

theorem lower_reach {config : Fin 7→UnitTriangle} (h : Normalized config) (i : Fin 6) :
    1-M h ≤ a h.cover i := ((structure_bounds h).1 i).trans (min_le_left _ _)

theorem join_one {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i↔i=4) : 1-a h.cover 2 ≤ b h.cover 1 := by
  have hh := le_of_not_gt (SoleGapArea.no_prefix_gap h sole 1)
  change 1 ≤ b h.cover 1+a h.cover 2 at hh
  linarith

theorem join_two {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i↔i=4) : 1-a h.cover 3 ≤ b h.cover 2 := by
  have hh := le_of_not_gt (SoleGapArea.no_prefix_gap h sole 2)
  change 1 ≤ b h.cover 2+a h.cover 3 at hh
  linarith

theorem Qt_not_one_small {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i↔i=4)
    (hs : a h.cover 2 ≤ 6*(1-M h)/5) :
    E4InsideOwners.Qt (1-M h)∉(rotateConfig config 1).region := by
  intro hQ
  obtain ⟨ch⟩ := exists_chart h.cover 1
  have ht : 0<1-M h := by linarith [(structure_bounds h).2.2.2.2.1]
  have ht1 : 1-M h<2/25 := by
    linarith [GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩]
  have hrow := one_Qt_row h.cover ch hQ
  have hf := forward_tests h.cover 1 ch
  have ha := lower_reach h 1
  have hb := join_one h sole
  by_cases hr : 0 ≤ ch.r
  · exact nonnegative_upper_impossible hr ch.D_pos ch.D_sq ht ht1
      (E4InsideArea.a2_lt_twenty_three h sole) ha hb hf.2.1 hrow ch.margin_sum
  · have hr1 : ch.r<0 := lt_of_not_ge hr
    have hr0 := one_Qt_slope_lower h sole ch ht ht1 hQ
    have he := negative_forward h.cover 1 ch hr0 hr1
    have hsq : ch.D^2=1-(-ch.r)+(-ch.r)^2 := by nlinarith only [ch.D_sq]
    have hrow' : 1-2*(1-M h)/3-(-ch.r)*(1-4*(1-M h)/3) ≤ b h.cover 1 := by
      rw [he] at hrow
      nlinarith only [hrow]
    have hsum : a h.cover 1+ch.d+b h.cover 1=ch.D := by simpa only [he] using ch.margin_sum
    exact negative_upper_impossible (by linarith) (by linarith) ch.D_pos hsq
      ht ht1 hs ha hb ch.d_pos hrow' hsum

/-- Conditional owner branch closed: the actual Pa cannot be in closed T3.
A remains an explicit intermediate duty; E4Outside later supplies it. -/
theorem actual_Pa_not_three {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i↔i=4)
    (hA : point (-19/100) 0∈(rotateConfig config 2).region) :
    E4InsideCentral.Pa (a h.cover 5)∉(rotateConfig config 3).region := by
  intro hPa
  obtain ⟨ch⟩ := exists_chart h.cover 2
  have hLa := E4T3Actual.actual_lower_duty h sole hPa
  have hrow := two_La_row h.cover ch hLa
  have ht : 0<1-M h := by linarith [(structure_bounds h).2.2.2.2.1]
  have ht1 : 1-M h<2/25 := by
    linarith [GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩]
  have ha : 0<a h.cover 5 := (leftReach h.cover 5).positive
  have hat := GapChains.heavy_short h
  have hs := lower_reach h 2
  have has : a h.cover 5/2<a h.cover 2 := by linarith
  have hs1 := E4InsideArea.a2_lt_twenty_three h sole
  have hf := forward_tests h.cover 2 ch
  by_cases hr : 0 ≤ ch.r
  · exact nonnegative_lower_impossible hr ch.D_pos ch.D_sq has ha
      (E4InsideArea.a3_lt_third h sole) (join_two h sole) hf.2.1 hrow ch.margin_sum
  · have hr1 : ch.r<0 := lt_of_not_ge hr
    obtain ⟨hr0,hrbound⟩ := two_slope_lower h sole ch hA
    have he := negative_forward h.cover 2 ch hr0 hr1
    have hsq : ch.D^2=1-(-ch.r)+(-ch.r)^2 := by nlinarith only [ch.D_sq]
    have hexi := ReachEndpoints.actual_exit_constraint h.cover 5
    change (a h.cover 5)^2+(a h.cover 5)*M h+(M h)^2 ≤ 1 at hexi
    have hexi' : (a h.cover 5)^2+(a h.cover 5)*(1-(1-M h))+(1-(1-M h))^2 ≤ 1 := by
      convert hexi using 1 <;> ring
    have hsep := heavy_separation ht ht1 hat hexi'
    have hG : 2*(a h.cover 2)-a h.cover 5-(a h.cover 5)*(-ch.r)-(-ch.r)+
        2*(1-ch.D)<0 := by nlinarith only [ch.margin_sum,ch.d_pos,hrow]
    by_cases hsmall : a h.cover 2 ≤ 6*(1-M h)/5
    · have hQ := (E4InsideOwners.actual_Qt_union h sole).resolve_left
        (Qt_not_one_small h sole hsmall)
      have hQrow := two_Qt_row h.cover ch hQ
      have hk := upper_slope ht ht1 hsmall (show 2*(1-M h)/3+(-ch.r)*(1-4*(1-M h)/3) ≤ a h.cover 2 by
        nlinarith only [hQrow])
      exact small_lower_impossible ht ht1 hs ha hat hsep (by linarith) (by linarith)
        hk ch.D_pos hsq hG
    · exact large_lower_impossible ht ht1 (le_of_not_ge hsmall) hs1 ha hat hsep
        (by linarith) (by linarith) hrbound ch.D_pos hsq hG

#print axioms Qt_not_one_small
#print axioms actual_Pa_not_three
end
end HexagonCover.E4InsideActualSeam
