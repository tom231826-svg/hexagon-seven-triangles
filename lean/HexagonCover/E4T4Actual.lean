import HexagonCover.E4T4Chart
import HexagonCover.E4T4Points
import HexagonCover.E4T4Boundary
import HexagonCover.E4InsideMidpoint

/-! Actual same-configuration T4 exclusion. The positive and negative
contacts use a supporting halfplane and covering, so no unproved finite-edge
incidence premise is needed. The negative branch uses the independently
proved v>=3a/4 central obstruction instead of the old polar-cone argument. -/
namespace HexagonCover.E4T4Actual
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
open E4InsideRayChart E4InsideActualChart TriangleFrame E4T4Chart E4T4Points
local notation "h₀" => NICertificate.halfRoot

theorem positive_line {r e v : ℝ} (hv : (1+2*r)*v=1+r-e) :
    dotp (normal r) (positivePoint v)=e-1-r := by
  have hh := ne_of_gt ExtremeTriangle.halfRoot_pos
  have he : dotp (normal r) (positivePoint v)=-(1+2*r)*v := by
    dsimp [dotp,E4T4Chart.normal,positivePoint]
    field_simp [hh]
    ring
  rw [he]
  linarith

theorem negative_line {k b v : ℝ} (hv : (2-k)*v=2-k-2*b) :
    dotp (normal (-k)) (midpoint v)=b-1+k := by
  have hh := ne_of_gt ExtremeTriangle.halfRoot_pos
  have he : dotp (normal (-k)) (midpoint v)=k/2-(2-k)*v/2 := by
    dsimp [dotp,E4T4Chart.normal,E4T4Points.midpoint]
    field_simp [hh]
    ring
  rw [he]
  linarith

theorem positive_impossible {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (ch : Chart (rotateConfig config 4) (vertex 4) (back 4) (forward 4) (a h.cover 4))
    (hp : E4InsideCentral.Pa (a h.cover 5)∈interior (rotateConfig config 4).region)
    (hr : 0<ch.r) (hd : ch.d=ch.r*b h.cover 4) : False := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  have hPa := (Pa_tests ch hp).2
  have hsum := ch.margin_sum
  rw [hd] at hsum
  let v : ℝ := (1+ch.r-ch.e)/(1+2*ch.r)
  have hden : 0<1+2*ch.r := by linarith
  have hv : (1+2*ch.r)*v=1+ch.r-ch.e := by
    dsimp [v]
    field_simp [ne_of_gt hden]
  obtain ⟨hap,hpv,hva⟩ := E4T4Scalar.positive_contact_bounds ha ha1
    (actual_short_lt_four h) (SoleGapArea.b4_half h sole) hr ch.D_pos.le
    ch.D_sq hsum hPa hv
  have hv0 : 0<v := by linarith
  have hc : positivePoint v∈(rotateConfig config 6).region := by
    apply E4T4Boundary.supporting_line_forced (covered h.cover) (owner:=4)
      (positive_interior hv0 (by linarith)) (normal_pos (by linarith))
      (positive_line hv) (actual_positive_others h sole hpv hva)
    exact halfplane ch
  exact E4InsideDisk.actual_contact_excluded h sole (by linarith) hc

theorem negative_impossible {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4)
    (ch : Chart (rotateConfig config 4) (vertex 4) (back 4) (forward 4) (a h.cover 4))
    (hp : E4InsideCentral.Pa (a h.cover 5)∈interior (rotateConfig config 4).region)
    (hr0 : -1/2<ch.r) (hr : ch.r<0) (he : ch.e=b h.cover 4) : False := by
  obtain ⟨ha,ha1⟩ := E4InsideCentral.actual_a_bounds h sole
  have hPa := (Pa_tests ch hp).1
  have hsum := ch.margin_sum
  rw [he] at hsum
  have hgap := (sole 4).mpr rfl
  change b h.cover 4+a h.cover 5<1 at hgap
  let k : ℝ := -ch.r
  have hk : 0<k := neg_pos.mpr hr
  have hk1 : k<1/2 := by dsimp [k]; linarith
  have hden : 0<2-k := by linarith
  let v : ℝ := (2-k-2*b h.cover 4)/(2-k)
  have hv : (2-k)*v=2-k-2*b h.cover 4 := by
    dsimp [v]
    field_simp [ne_of_gt hden]
  have hsq : ch.D^2=1-k+k^2 := by dsimp [k]; nlinarith only [ch.D_sq]
  obtain ⟨hva,hv1⟩ := E4T4Scalar.negative_contact_bounds (b:=b h.cover 4) ha ha1 hk hk1
    (rightReach h.cover 4).positive (by linarith)
    (show a h.cover 5/2+k*(1-a h.cover 5)<a h.cover 4 by
      dsimp [k]; nlinarith only [hPa])
    (show a h.cover 4+b h.cover 4<ch.D by linarith [ch.d_pos])
    ch.D_pos.le hsq hv
  have hv0 : 0<v := by linarith
  have hline : dotp (normal ch.r) (midpoint v)=ch.e-1-ch.r := by
    have hh := negative_line hv
    dsimp [k] at hh
    simpa only [neg_neg,he,sub_eq_add_neg] using hh
  have hc : midpoint v∈(rotateConfig config 6).region :=
    E4T4Boundary.supporting_line_forced (covered h.cover) (owner:=4)
      (midpoint_interior hv0 hv1) (normal_pos hr0) hline
      (actual_midpoint_others h sole hv0) (halfplane ch)
  exact E4InsideMidpoint.actual_midpoint_excluded h sole hva.le hc

/-- All actual T4 orientations, including active-row ties, are derived and
excluded. There are no chart/contact assumptions in this conclusion. -/
theorem Pa_not_interior_four {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) :
    E4InsideCentral.Pa (a h.cover 5)∉interior (rotateConfig config 4).region := by
  intro hp
  obtain ⟨ch⟩ := exists_chart h.cover 4
  obtain ⟨hr0,hcases⟩ := actual_cases h sole ch hp
  rcases hcases with ⟨hr,he⟩ | ⟨hr,hd⟩
  · exact negative_impossible h sole ch hp hr0 hr he
  · exact positive_impossible h sole ch hp hr hd

#print axioms Pa_not_interior_four
end
end HexagonCover.E4T4Actual
