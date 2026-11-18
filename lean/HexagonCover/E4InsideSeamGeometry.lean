import HexagonCover.E4InsideActualChart
import HexagonCover.E4InsideArea
import HexagonCover.E4InsideSeamScalar

/-! Necessary T1/T2 rows from the SAME actual placement. Active-side ties
are preserved by ActualChart, and the negative branch selects its forward
side only after the other two are excluded by signs. -/
namespace HexagonCover.E4InsideSeamGeometry
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
open E4InsideRayChart E4InsideActualChart
local notation "h₀" => NICertificate.halfRoot

abbrev ActualChart {config : Fin 7→UnitTriangle} (h : StrictCover config) (i : Fin 6) :=
  Chart (rotateConfig config i.castSucc) (vertex i) (back i) (forward i) (a h i)

theorem negative_forward {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (i : Fin 6) (ch : ActualChart h i) (hr0 : -1/2<ch.r) (hr1 : ch.r<0) :
    ch.e=b h i := by
  have hb : 0<b h i := (rightReach h i).positive
  have hfirst : -(1+ch.r)*b h i<0 := mul_neg_of_neg_of_pos (by linarith) hb
  have hsecond : ch.r*b h i<0 := mul_neg_of_neg_of_pos hr1 hb
  rcases forward_active h i ch with he|he|he
  · linarith [ch.first_pos]
  · linarith [ch.d_pos]
  · exact he.symm

theorem one_point (L K : ℝ) : vertex 1+L • back 1+K • forward 1=
    point (-1/2+L-K/2) (h₀*(1-K)) := by
  ext i
  fin_cases i <;> norm_num [back,forward,vertex_table] <;> ring

theorem two_point (L K : ℝ) : vertex 2+L • back 2+K • forward 2=
    point (-1+(L+K)/2) (h₀*(L-K)) := by
  ext i
  fin_cases i <;> norm_num [back,forward,vertex_table] <;> ring

theorem two_A_row {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (ch : ActualChart h 2)
    (hA : point (-19/100) 0∈(rotateConfig config 2).region) :
    -(81/100)*ch.r ≤ a h 2 := by
  have he : vertex 2+(81/100:ℝ) • back 2+(81/100:ℝ) • forward 2=
      point (-19/100) 0 := by rw [two_point]; norm_num
  have ht := (ch.character (81/100) (81/100)).mp (he.symm ▸ hA) 0
  simp only [rows,Matrix.cons_val_zero] at ht
  nlinarith only [ht]

theorem two_slope_lower {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i↔i=4) (ch : ActualChart h.cover 2)
    (hA : point (-19/100) 0∈(rotateConfig config 2).region) :
    -1/2<ch.r ∧ -ch.r ≤ 100*(a h.cover 2)/81 := by
  have hr := two_A_row h.cover ch hA
  have hs := E4InsideArea.a2_lt_twenty_three h sole
  constructor <;> linarith

/-- When Qt is actually in T1, its first row itself gives the needed negative
slope bound. The source's separate Zplus packet is unnecessary for this duty. -/
theorem one_Qt_slope_lower {config : Fin 7→UnitTriangle} (h : Normalized config)
    (sole : ∀i,BoundaryGaps.gap h.cover i↔i=4) (ch : ActualChart h.cover 1)
    {t : ℝ} (ht : 0<t) (ht1 : t<2/25)
    (hQ : point (-t) (2*h₀*t/3)∈(rotateConfig config 1).region) : -1/2<ch.r := by
  have he : vertex 1+(1-4*t/3) • back 1+(1-2*t/3) • forward 1=
      point (-t) (2*h₀*t/3) := by
    rw [one_point]
    congr 1 <;> ring
  have hh := (ch.character (1-4*t/3) (1-2*t/3)).mp (he.symm ▸ hQ) 0
  simp only [rows,Matrix.cons_val_zero] at hh
  have ha := SoleGapArea.a1_fifth h sole
  by_contra hn
  have hr : ch.r ≤ -1/2 := le_of_not_gt hn
  have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ 1-2*t/3 by linarith)
  nlinarith only [hh,ha,hm,ht1]

theorem two_La_row {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (ch : ActualChart h 2) {a₅ : ℝ}
    (hp : point (-1/4) (h₀*(a₅-1/2))∈(rotateConfig config 2).region) :
    1-a₅/2+ch.r*(1+a₅)/2 ≤ ch.e := by
  have he : vertex 2+((1+a₅)/2) • back 2+(1-a₅/2) • forward 2=
      point (-1/4) (h₀*(a₅-1/2)) := by
    rw [two_point]
    congr 1 <;> ring
  have ht := (ch.character ((1+a₅)/2) (1-a₅/2)).mp (he.symm ▸ hp) 2
  simpa [rows,mul_div_assoc,add_comm] using ht

theorem one_Qt_row {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (ch : ActualChart h 1) {t : ℝ}
    (hp : point (-t) (2*h₀*t/3)∈(rotateConfig config 1).region) :
    1-2*t/3+ch.r*(1-4*t/3) ≤ ch.e := by
  have he : vertex 1+(1-4*t/3) • back 1+(1-2*t/3) • forward 1=
      point (-t) (2*h₀*t/3) := by
    rw [one_point]
    congr 1 <;> ring
  have ht := (ch.character (1-4*t/3) (1-2*t/3)).mp (he.symm ▸ hp) 2
  simpa [rows,add_comm] using ht

theorem two_Qt_row {config : Fin 7→UnitTriangle} (h : StrictCover config)
    (ch : ActualChart h 2) {t : ℝ}
    (hp : point (-t) (2*h₀*t/3)∈(rotateConfig config 2).region) :
    2*t/3-ch.r*(1-4*t/3) ≤ a h 2 := by
  have he : vertex 2+(1-2*t/3) • back 2+(1-4*t/3) • forward 2=
      point (-t) (2*h₀*t/3) := by
    rw [two_point]
    congr 1 <;> ring
  have ht := (ch.character (1-2*t/3) (1-4*t/3)).mp (he.symm ▸ hp) 0
  simp only [rows,Matrix.cons_val_zero] at ht
  nlinarith only [ht]

#print axioms two_slope_lower
#print axioms one_Qt_slope_lower
end
end HexagonCover.E4InsideSeamGeometry
