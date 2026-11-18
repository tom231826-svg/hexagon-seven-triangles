import HexagonCover.CentralRadius

/-! Exact scalar deficit bound for the central finite-side trace.
The actual-pose hypotheses are derived separately in CentralTrace. -/
namespace HexagonCover.TraceAlgebra
noncomputable section
local notation "h₀" =>  NICertificate.halfRoot

def den (z : ℝ) : ℝ := h₀*(1-z^2)+z

def firstCoefficient (z : ℝ) : ℝ := (5/2-2*h₀*z+3/2*z^2)/(2*den z)
def secondCoefficient (z : ℝ) : ℝ := h₀*(1-z^4)/den z

theorem parameter_lt_one {z : ℝ} (hz : 0 < z) (hu : 2*h₀*z ≤ 1) : z < 1 := by
  have hh := ExtremeTriangle.halfRoot_sq
  have hp := ExtremeTriangle.halfRoot_pos
  have hhalf : 1/2 < h₀ := by nlinarith
  nlinarith [mul_pos hz (show 0 < 2*h₀-1 by linarith)]

theorem den_pos {z : ℝ} (hz : 0 < z) (hu : 2*h₀*z ≤ 1) : 0 < den z := by
  have h1 := parameter_lt_one hz hu
  have hs : 0 < 1-z^2 := by nlinarith
  exact add_pos (mul_pos ExtremeTriangle.halfRoot_pos hs) hz

theorem firstCoefficient_lower {z : ℝ} (hz : 0 < z) (hu : 2*h₀*z ≤ 1) :
    h₀ ≤ firstCoefficient z := by
  unfold firstCoefficient
  apply (le_div_iff₀ (mul_pos (by norm_num) (den_pos hz hu))).mpr
  have hs := ExtremeTriangle.halfRoot_sq
  have hm := congrArg (fun v : ℝ =>  z^2*v) hs
  unfold den
  nlinarith [sq_nonneg (1-2*h₀*z)]

theorem quartic_nonneg {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ 3-4*w+2*w^2-w^4 := by
  have hb : 0 ≤ w^3+w^2-w+3 := by nlinarith [pow_nonneg hw0 3,sq_nonneg w]
  have hm := mul_nonneg (sub_nonneg.mpr hw1) hb
  nlinarith only [hm]

theorem halfRoot_cube : h₀^3=3/4*h₀ := by
  calc
    _ = h₀^2*h₀ := by ring
    _ = _ := by rw [ExtremeTriangle.halfRoot_sq]

theorem halfRoot_fifth : h₀^5=9/16*h₀ := by
  calc
    _ = (h₀^2)^2*h₀ := by ring
    _ = _ := by rw [ExtremeTriangle.halfRoot_sq]; ring

theorem secondCoefficient_lower {z : ℝ} (hz : 0 < z) (hu : 2*h₀*z ≤ 1) :
    2/3 ≤ secondCoefficient z := by
  have hp := ExtremeTriangle.halfRoot_pos
  unfold secondCoefficient
  apply (le_div_iff₀ (den_pos hz hu)).mpr
  have hh := ExtremeTriangle.halfRoot_sq
  have hquart := quartic_nonneg (by positivity : 0 ≤ 2*h₀*z) hu
  have he : 3*h₀*(1-z^4)-2*den z =
      h₀/3*(3-4*(2*h₀*z)+2*(2*h₀*z)^2-(2*h₀*z)^4) := by
    unfold den
    ring_nf
    simp only [hh,halfRoot_cube,halfRoot_fifth]
    ring
  have hm := mul_nonneg (by positivity : 0 ≤ h₀/3) hquart
  rw [←he] at hm
  linarith

theorem amgm_radius {z r : ℝ} (hz : 0 < z) (hr : 0 ≤ r) :
    Real.sqrt (8*h₀*r/3) ≤ h₀*z+2*r/(3*z) := by
  have hp := ExtremeTriangle.halfRoot_pos
  have ha : 0 ≤ h₀*z := by positivity
  have hb : 0 ≤ 2*r/(3*z) := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg ha hb)).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ 8*h₀*r/3)]
  have he : (h₀*z)*(2*r/(3*z))=2*h₀*r/3 := by field_simp <;> ring
  nlinarith [sq_nonneg (h₀*z-2*r/(3*z))]

theorem deficit_lower {z r : ℝ} (hz : 0 < z) (hu : 2*h₀*z ≤ 1) (hr : 0 ≤ r) :
    Real.sqrt (8*h₀*r/3) ≤ z*firstCoefficient z+(r/z)*secondCoefficient z := by
  have hfirst := mul_le_mul_of_nonneg_left (firstCoefficient_lower hz hu) hz.le
  have hsecond := mul_le_mul_of_nonneg_left (secondCoefficient_lower hz hu) (div_nonneg hr hz.le)
  have hamgm := amgm_radius hz hr
  have he : h₀*z+2*r/(3*z)=z*h₀+(r/z)*(2/3) := by field_simp <;> ring
  rw [he] at hamgm
  linarith

/-- Exact half-angle deficit identity, before applying the two inequalities. -/
theorem deficit_identity {z r : ℝ} (hz : z≠0) (hd : den z≠0) :
    1/2-h₀*((h₀*NI.circleX z+NI.circleY z/2)-2*r*NI.circleX z-h₀)/
      ((h₀*NI.circleX z+NI.circleY z/2)*NI.circleY z) =
    z*firstCoefficient z+(r/z)*secondCoefficient z := by
  have hd' : h₀*(1-z^2)+z≠0 := hd
  have hh := ExtremeTriangle.halfRoot_sq
  unfold NI.circleX NI.circleY firstCoefficient secondCoefficient den
  field_simp
  ring_nf
  simp only [hh,halfRoot_cube,halfRoot_fifth]
  ring

/-- Conditional scalar cap envelope; actual side geometry must supply c,s,Y. -/
theorem cap_bound {c s Y r : ℝ} (hc : 1/2 ≤ c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (hr : 0 ≤ r)
    (hY : Y ≤ h₀*c+s/2-2*r*c) :
    h₀*(Y-h₀)/((h₀*c+s/2)*s) ≤ 1/2-Real.sqrt (8*h₀*r/3) := by
  have hp := ExtremeTriangle.halfRoot_pos
  let z := s/(1+c)
  have hden : 0 < 1+c := by linarith
  have hz : 0 < z := div_pos hs hden
  have hc0 : 0 ≤ c := by linarith
  have hcx : NI.circleX z=c := NI.chart_reconstruct_x hunit hc0
  have hsy : NI.circleY z=s := NI.chart_reconstruct_y hunit hc0
  have hh := ExtremeTriangle.halfRoot_sq
  have hbound : 2*h₀*s ≤ 1+c := by
    have hleft : 0 ≤ 2*h₀*s := by positivity
    apply (sq_le_sq₀ hleft hden.le).mp
    have hm := congrArg (fun v : ℝ =>  s^2*v) hh
    nlinarith [sq_nonneg (c-1/2)]
  have hu : 2*h₀*z ≤ 1 := by
    dsimp [z]
    rw [←mul_div_assoc]
    exact (div_le_one hden).mpr hbound
  have hd := den_pos hz hu
  have hi := deficit_identity (r:=r) (ne_of_gt hz) (ne_of_gt hd)
  rw [hcx,hsy] at hi
  have hb := deficit_lower hz hu hr
  have hprod : 0 < (h₀*c+s/2)*s := by positivity
  have hcap : h₀*(Y-h₀)/((h₀*c+s/2)*s) ≤ 
      h₀*((h₀*c+s/2)-2*r*c-h₀)/((h₀*c+s/2)*s) := by
    apply div_le_div_of_nonneg_right _ hprod.le
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hY _) ExtremeTriangle.halfRoot_pos.le
  linarith

end
end HexagonCover.TraceAlgebra
