import HexagonCover.GapScale
import HexagonCover.CentralTrace

/-! Gap width and adjacent-gap diameter constraints for the same actual C.
These are source-exposed lemmas from b3-Gs-proof §§1,3,5. -/
namespace HexagonCover.GapChains
open Configuration NormalizedHeavy BoundaryGaps BoundaryOwners
noncomputable section

theorem quadratic_short {x t : ℝ} (ht : 0  <  t) (ht1 : t  <  1) (hx : 0  ≤  x)
    (hp : x^2+(1-t)*x+(1-t)^2  ≤  1) : x  <  2*t := by
  by_contra hn
  have hl : 2*t  ≤  x := le_of_not_gt hn
  have hs := pow_le_pow_left₀ (by positivity : 0  ≤  2*t) hl 2
  have hm := mul_le_mul_of_nonneg_left hl (show 0  ≤  1-t by linarith)
  nlinarith [sq_pos_of_pos ht]

theorem heavy_short {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    a h.cover 5  <  2*(1-M h) := by
  have hb := structure_bounds h
  have hp := ReachEndpoints.actual_exit_constraint h.cover 5
  apply quadratic_short (x:=a h.cover 5) (t:=1-M h) (by linarith [hb.2.2.2.2.1])
    (by linarith [hb.2.2.2.1]) (leftReach h.cover 5).positive.le
  change (a h.cover 5)^2+a h.cover 5*M h+(M h)^2  ≤  1 at hp
  nlinarith only [hp]

theorem trace_sqrt_gt_two {t : ℝ} (ht : 0  <  t) (ht1 : t  <  (1:ℝ)/5) :
    2*t  <  Real.sqrt (8*NICertificate.halfRoot*CommonReach.rho t/3) := by
  have hp := IntruderReach.rho_gt_safe_radius ht (by linarith)
  have hp0 := (CentralDisk.rho_bounds ht (by linarith)).1
  have hz : 2*t^2  <  CommonReach.rho t := by
    nlinarith [mul_pos ht (show 0  <  1-5*t by linarith)]
  have hh0 := ExtremeTriangle.halfRoot_pos
  have hh := ExtremeTriangle.halfRoot_sq
  have hhlo : (3:ℝ)/4  <  NICertificate.halfRoot := by nlinarith
  have hrad : 0  ≤  8*NICertificate.halfRoot*CommonReach.rho t/3 := by positivity
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (8*NICertificate.halfRoot*CommonReach.rho t/3)
  have hm := mul_lt_mul_of_pos_right hhlo hp0
  nlinarith only [hz,hs,hs0,hm,ht]

theorem gap_width {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (i : Fin 6) (hi : gap h.cover i) :
    1/2+Real.sqrt (8*NICertificate.halfRoot*CommonReach.rho (1-M h)/3)  ≤ 
      b h.cover i+a h.cover (i+1) := by
  have hb := structure_bounds h
  have ht0 : 0  <  1-M h := by linarith [hb.2.2.2.2.1]
  have ht1 : 1-M h  <  1 := by linarith [hb.2.2.2.1]
  have disk := CentralDisk.actual_central_disk_of_reach_lower h.cover ht0 ht1 hb.1
  have hjoin : b h.cover i  ≤  1-a h.cover (i+1) := by
    change b h.cover i+a h.cover (i+1) < 1 at hi
    linarith
  have hleft := closed_gap_central h.cover i hi (b h.cover i) ⟨le_rfl,hjoin⟩
  have hright := closed_gap_central h.cover i hi (1-a h.cover (i+1)) ⟨hjoin,le_rfl⟩
  have hs := CentralTrace.edge_parameter_trace (config 6)
    (CentralDisk.rho_bounds ht0 ht1).1 disk i hright hleft
  rw [abs_of_nonneg (by linarith : 0  ≤  (1-a h.cover (i+1))-b h.cover i)] at hs
  linarith

theorem adjacent_gap_constraint {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hprev : gap h (i-1)) (hi : gap h i) :
    (1-b h (i-1))^2+(1-b h (i-1))*(1-a h (i+1))+(1-a h (i+1))^2  ≤  1 := by
  have hprevjoin : b h (i-1)  ≤  1-a h ((i-1)+1) := by
    change b h (i-1)+a h ((i-1)+1) < 1 at hprev
    linarith
  have hjoin : b h i  ≤  1-a h (i+1) := by
    change b h i+a h (i+1) < 1 at hi
    linarith
  have hp := closed_gap_central h (i-1) hprev (b h (i-1)) ⟨le_rfl,hprevjoin⟩
  have hq := closed_gap_central h i hi (1-a h (i+1)) ⟨hjoin,le_rfl⟩
  rw [reversed_edge,sub_add_cancel] at hp
  have hd := (config 6).dist_le_one hp hq
  have he := ReachEndpoints.two_exit_distance i (1-b h (i-1)) (1-a h (i+1))
  have hn := dist_nonneg
    (x:=AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) (1-b h (i-1)))
    (y:=edgePoint i (1-a h (i+1)))
  dsimp only [edgePoint] at hd hn
  nlinarith only [hd,he,hn]

theorem adjacent_before_half {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hprev : gap h (i-1)) (hi : gap h i)
    (ha : a h (i+1)  <  (1:ℝ)/5) : (1:ℝ)/2  <  b h (i-1) := by
  have hpoly := adjacent_gap_constraint h i hprev hi
  have hs := quadratic_short (x:=1-b h (i-1)) (t:=a h (i+1))
    (leftReach h (i+1)).positive (leftReach h (i+1)).lt_one
    (by have hb : b h (i-1) < 1 := (rightReach h (i-1)).lt_one; linarith only [hb]) (by nlinarith only [hpoly])
  linarith

end
end HexagonCover.GapChains
