import HexagonCover.NoGapChain
import HexagonCover.SourceCoordinates

/-! Necessary scalar/radius conditions for the frozen N packets, all attached
to the same actual normalized configuration and its whole physical rotation. -/
namespace HexagonCover.NPacketBounds
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
noncomputable section

theorem central_safe_radius {config : Fin 7 → UnitTriangle} (h : Normalized config)
    {U : ℝ} (hU0 : 0 < U) (hU1 : U < 1) (hMU : M h ≤ U) :
    Metric.closedBall (0:Plane) ((1-U)*U/2) ⊆ (rotateConfig config 6).region := by
  let t := 1-U
  have ht0 : 0 < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have lower : ∀i,t ≤ min (a h.cover i) (b h.cover i) := by
    intro i
    have hi := (structure_bounds h).1 i
    dsimp [t]
    linarith
  have disk := CentralDisk.actual_central_disk_of_reach_lower h.cover ht0 ht1 lower
  have hs := IntruderReach.rho_gt_safe_radius ht0 ht1
  have hrad : (1-U)*U/2 ≤ CommonReach.rho t := by dsimp [t] at hs; nlinarith only [hs]
  exact central_disk ((Metric.closedBall_subset_closedBall hrad).trans disk)

theorem heavy_radius_sq {config : Fin 7 → UnitTriangle} (h : Normalized config)
    {L : ℝ} (hL : 0 ≤ L) (hLM : L ≤ M h) :
    ∀p∈(rotateConfig config 5).region, 3*L^2/4 ≤ ‖p‖^2 := by
  obtain ⟨D,hD,_,hP⟩ := HeavyTransport.actual_heavy_separation h.cover 5 h.heavy5
  rw [max_eq_M h] at hD
  have hs : ∀p∈(config 5).region,NICertificate.halfRoot*L ≤ ‖p‖ := by
    intro p hp
    exact (mul_le_mul_of_nonneg_left hLM ExtremeTriangle.halfRoot_pos.le).trans
      (hD.trans (hP p hp))
  have ht := separation (config:=config) 5 hs
  intro p hp
  have he := ht p hp
  have hnon : 0 ≤ NICertificate.halfRoot*L := mul_nonneg ExtremeTriangle.halfRoot_pos.le hL
  have hsq := pow_le_pow_left₀ hnon he 2
  rw [mul_pow,ExtremeTriangle.halfRoot_sq] at hsq
  nlinarith only [hsq]

theorem five_step_sum (j : Fin 5) (x y : ℝ) :
    (∑i:Fin 5,if i<j then x else y)=(j.val:ℝ)*x+(5-(j.val:ℝ))*y := by
  fin_cases j <;> norm_num [Fin.sum_univ_succ] <;> ring

theorem area_window {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i)
    {L U : ℝ} (hL : 0 ≤ L) (hLM : L ≤ M h) (hMU : M h ≤ U) (hU1 : U ≤ 1)
    (j : Fin 5) :
    L^2+(j.val:ℝ)*(1-U)^2+(5-(j.val:ℝ))*(a h.cover j.castSucc)^2 ≤ 1 := by
  have ht : 0 ≤ 1-U := by linarith
  have hmono := (NoGapChain.a_strictMono h nogaps).monotone
  have hpoint (i : Fin 5) :
      (if i<j then (1-U)^2 else (a h.cover j.castSucc)^2) ≤ (a h.cover i.castSucc)^2 := by
    split_ifs with hi
    · have hl := ((structure_bounds h).1 i.castSucc).trans (min_le_left _ _)
      have hlow : 1-U ≤ a h.cover i.castSucc := by linarith
      exact pow_le_pow_left₀ ht hlow 2
    · have hij : j.castSucc ≤ i.castSucc := by
        have hh := le_of_not_gt hi
        exact hh
      exact pow_le_pow_left₀ (leftReach h.cover j.castSucc).positive.le (hmono hij) 2
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hpoint i)
  rw [five_step_sum] at hs
  have hLM2 := pow_le_pow_left₀ hL hLM 2
  have hb := NoGapChain.actual_area_window h nogaps
  linarith


theorem endpoint_upper {config : Fin 7 → UnitTriangle} (h : Normalized config)
    {L f : ℝ} (hL : 0 ≤ L) (hLM : L ≤ M h) (hf : 0 ≤ f)
    (hpoly : 1 ≤ f^2+L*f+L^2) : a h.cover 5 ≤ f := by
  have hc := ReachEndpoints.actual_exit_constraint h.cover 5
  change (a h.cover 5)^2+a h.cover 5*M h+(M h)^2 ≤ 1 at hc
  have ha : 0 ≤ a h.cover 5 := (leftReach h.cover 5).positive.le
  have hm := mul_le_mul_of_nonneg_left hLM ha
  have hm2 := pow_le_pow_left₀ hL hLM 2
  have hsmall : (a h.cover 5)^2+L*a h.cover 5+L^2 ≤ 1 := by nlinarith only [hc,hm,hm2]
  by_contra hn
  have hgt : f < a h.cover 5 := lt_of_not_ge hn
  have hs : f^2 < (a h.cover 5)^2 := (sq_lt_sq₀ hf ha).mpr hgt
  have hprod := mul_le_mul_of_nonneg_left hgt.le hL
  linarith

theorem scalar_window_upper {c x w B : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hw : 0 ≤ w)
    (hbound : c*x^2 ≤ B) (hwide : B ≤ c*w^2) : x ≤ w := by
  have hs : x^2 ≤ w^2 := (mul_le_mul_iff_right₀ hc).mp (hbound.trans hwide)
  exact (sq_le_sq₀ hx hw).mp hs

end
end HexagonCover.NPacketBounds
