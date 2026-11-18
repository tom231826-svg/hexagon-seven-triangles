import HexagonCover.ReachTransport

/-! The same central triangle contains the disk excluded by all six actual
outer triangles. No central piece from another configuration is substituted. -/
namespace HexagonCover.CentralDisk
open HexagonCover.Configuration
noncomputable section

theorem small_closed_ball_hexagon {r : ℝ} (hr : r ≤ (1:ℝ)/2) :
    Metric.closedBall (0 : Plane) r ⊆ Hexagon 1 := by
  intro p hp
  have hn : ‖p‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
  have hsq := norm_point_sq (p 0) (p 1)
  have he : point (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  rw [he] at hsq
  have hroot := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hrootpos := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)
  have hnorm := norm_nonneg p
  apply mem_hexagon_of_coordinate_bounds (by norm_num : (0:ℝ) < 1)
  · constructor <;> nlinarith [sq_nonneg (p 1)]
  · constructor <;> nlinarith [sq_nonneg (p 0)]

theorem closed_disk_of_outer_separation {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ (1:ℝ)/2)
    (sep : ∀ i : Fin 6, ∀ p ∈ (config i.castSucc).region, r ≤ ‖p‖) :
    Metric.closedBall (0 : Plane) r ⊆ (config 6).region := by
  have hopen : Metric.ball (0 : Plane) r ⊆ (config 6).region := by
    intro p hp
    have hh := small_closed_ball_hexagon hr1 (Metric.ball_subset_closedBall hp)
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (h.covered hh)
    by_cases he : j=6
    · simpa only [he] using hj
    · have hjlt : j.val < 6 := by omega
      let i : Fin 6 := ⟨j.val,hjlt⟩
      have hij : i.castSucc=j := by ext; rfl
      have hd := sep i p (by simpa only [hij] using hj)
      have hlt : ‖p‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hp
      linarith
  have hcl := (config 6).closed_region.closure_subset_iff.mpr hopen
  rw [closure_ball (0:Plane) hr0.ne'] at hcl
  exact hcl

theorem rho_bounds {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    0 < CommonReach.rho t ∧ CommonReach.rho t ≤ (1:ℝ)/2 := by
  have hr : 0 ≤ CommonReach.radiusSq t := by
    unfold CommonReach.radiusSq
    nlinarith [sq_nonneg (t-(1:ℝ)/2)]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (CommonReach.radiusSq t)
  have htprod := mul_pos ht0 (by linarith : 0<1-t)
  unfold CommonReach.rho CommonReach.radiusSq
  dsimp only [CommonReach.radiusSq] at hs hn
  constructor <;> nlinarith [sq_nonneg (t-(1:ℝ)/2)]

theorem actual_central_disk_of_reach_lower {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) {t : ℝ} (ht0 : 0<t) (ht1 : t<1)
    (lower : ∀ i, t ≤ min (a h i) (b h i)) :
    Metric.closedBall (0 : Plane) (CommonReach.rho t) ⊆ (config 6).region := by
  have hr := rho_bounds ht0 ht1
  exact closed_disk_of_outer_separation h hr.1 hr.2
    (fun i => ReachTransport.actual_reach_separation h i ht0.le (lower i))

end
end HexagonCover.CentralDisk
