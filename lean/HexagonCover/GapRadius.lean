import HexagonCover.BoundaryGaps
import HexagonCover.CentralRadius
import HexagonCover.CentralDisk

/-! Radius restrictions from the actual endpoints of a gap, in the same C. -/
namespace HexagonCover.GapRadius
open Configuration BoundaryOwners BoundaryGaps CentralRadius
noncomputable section

theorem edgePoint_norm_sq (i : Fin 6) (t : ℝ) :
    ‖edgePoint i t‖^2 = 1-t+t^2 := by
  have hs := TriangleFrame.dist_sq_coordinates (edgePoint i t) 0
  rw [dist_zero_right] at hs
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ)  ≤  3)
  generalize he : ‖edgePoint i t‖ = z at hs ⊢
  fin_cases i
  all_goals
    norm_num [edgePoint, hexVertex, AffineMap.lineMap_apply, point] at hs
    ring_nf at hs
    simp only [hr] at hs
    nlinarith only [hs]

theorem endpoints {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    {r : ℝ} (hr : 0 ≤ r) (disk : Metric.closedBall (0:Plane) r ⊆ (config 6).region)
    (i : Fin 6) (hi : gap h i) :
    r  ≤  IntruderReach.rmax (b h i)  ∧  r  ≤  IntruderReach.rmax (a h (i+1)) := by
  have hab : b h i  ≤  1-a h (i+1) := by
    change b h i+a h (i+1)<1 at hi
    linarith
  have hb := closed_gap_central h i hi (b h i) ⟨le_rfl,hab⟩
  have ha := closed_gap_central h i hi (1-a h (i+1)) ⟨hab,le_rfl⟩
  constructor
  · exact actual_endpoint_radius (config 6) hr disk hb (edgePoint_norm_sq i _).ge
  · have he := actual_endpoint_radius (config 6) hr disk ha (edgePoint_norm_sq i _).ge
    rwa [rmax_symm] at he

theorem gap_small {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    {r : ℝ} (hr : 0 ≤ r) (disk : Metric.closedBall (0:Plane) r ⊆ (config 6).region)
    (i : Fin 6) (hi : gap h i) : r < IntruderReach.rmax (1/2) := by
  have hab : b h i < 1-a h (i+1) := by
    change b h i+a h (i+1)<1 at hi
    linarith
  have exists_point : ∃t∈Set.Icc (b h i) (1-a h (i+1)), t ≠ (1:ℝ)/2 := by
    by_cases he : b h i=(1:ℝ)/2
    · exact ⟨1-a h (i+1),⟨hab.le,le_rfl⟩,by linarith⟩
    · exact ⟨b h i,⟨le_rfl,hab.le⟩,he⟩
  obtain ⟨t,ht,hneq⟩ := exists_point
  have hp : 3/4<‖edgePoint i t‖^2 := by
    rw [edgePoint_norm_sq]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hneq)]
  exact actual_beyond_apothem (config 6) hr disk (closed_gap_central h i hi t ht) hp

/-- A global minimum reach cannot be an endpoint of a positive gap. -/
theorem minimum_not_gap {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (lower : ∀ i, t ≤ min (a h i) (b h i)) (i : Fin 6)
    (endpoint : b h i=t  ∨  a h (i+1)=t) : ¬gap h i := by
  intro hi
  have disk := CentralDisk.actual_central_disk_of_reach_lower h ht ht1 lower
  have hb := endpoints h (CentralDisk.rho_bounds ht ht1).1.le disk i hi
  have hlt := IntruderReach.rho_gt_rmax ht ht1
  rcases endpoint with he | he
  · rw [he] at hb
    linarith [hb.1]
  · rw [he] at hb
    linarith [hb.2]

end
end HexagonCover.GapRadius
