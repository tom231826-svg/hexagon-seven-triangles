import HexagonCover.ContinuousSupportSymmetry
import HexagonCover.SupportGeometryWeak

/-! Weak real-parameter selected branches preserve equality and the strict
origin hypothesis. The candidate selections are never trusted as maxima. -/
namespace HexagonCover.ContinuousSupportWeak
noncomputable section
open SupportGeometry ContinuousSupport ContinuousSupportSymmetry SupportGeometryWeak

private theorem shift_origin {n : ℕ} (points : Fin (n+1) → Plane)
    (selected : Fin 3 → Fin (n+1)) (role : Fin 3)
    (h : ∃i,points (selected i)=0) : ∃i,points (shift role selected i)=0 := by
  obtain ⟨i,hi⟩ := h
  fin_cases role <;> fin_cases i
  all_goals first
    | exact ⟨0,hi⟩
    | exact ⟨1,hi⟩
    | exact ⟨2,hi⟩

theorem certificate {n : ℕ} (points : Fin (n+1) → Plane)
    (selected : Fin (n+1) → Fin (n+1) → Bool → Fin 3 → Fin (n+1))
    (checked : ∀j k, j < k → ∀negative,
      0 ≤ selectedSum points j k 0 negative (selected j k negative) ∧
      NICertificate.halfRoot^2*‖points k-points j‖^2 ≤
        (selectedSum points j k 0 negative (selected j k negative))^2 ∧
      (NICertificate.halfRoot^2*‖points k-points j‖^2 <
        (selectedSum points j k 0 negative (selected j k negative))^2 ∨
        ∃i,points (selected j k negative i)=0)) :
    OriginCertificate points NICertificate.halfRoot := by
  intro j k hjk role negative
  let f := extend selected j k role negative
  have hdata : 0 ≤ selectedSum points j k role negative f ∧
      NICertificate.halfRoot^2*‖points k-points j‖^2 ≤
        (selectedSum points j k role negative f)^2 ∧
      (NICertificate.halfRoot^2*‖points k-points j‖^2 <
        (selectedSum points j k role negative f)^2 ∨ ∃i,points (f i)=0) := by
    by_cases hlt : j < k
    · obtain ⟨h0,hs,hcase⟩ := checked j k hlt negative
      simp only [f,extend,hlt,↓reduceIte,selected_rotation]
      refine ⟨h0,hs,?_⟩
      exact hcase.imp id (shift_origin points _ role)
    · have hne : j≠k := fun he => hjk (congrArg points he)
      have hrev : k < j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      obtain ⟨h0,hs,hcase⟩ := checked k j hrev (!negative)
      simp only [f,extend,hlt,↓reduceIte,selected_rotation]
      have hswap := selected_swap points j k 0 negative (selected k j (!negative))
      rw [hswap,norm_sub_rev]
      refine ⟨h0,hs,?_⟩
      exact hcase.imp id (shift_origin points _ role)
  have hnonneg := mul_nonneg ExtremeTriangle.halfRoot_pos.le (norm_nonneg (points k-points j))
  apply rigidity_of_branch points f
  · apply (sq_le_sq₀ hnonneg hdata.1).mp
    simpa only [mul_pow] using hdata.2.1
  · rcases hdata.2.2 with hs | ho
    · left
      apply (sq_lt_sq₀ hnonneg hdata.1).mp
      simpa only [mul_pow] using hs
    · exact Or.inr ho

theorem impossible {n : ℕ} (points : Fin (n+1) → Plane)
    (hinj : Function.Injective points) {j k : Fin (n+1)} (hjk : j≠k)
    (selected : Fin (n+1) → Fin (n+1) → Bool → Fin 3 → Fin (n+1))
    (checked : ∀j k, j < k → ∀negative,
      0 ≤ selectedSum points j k 0 negative (selected j k negative) ∧
      NICertificate.halfRoot^2*‖points k-points j‖^2 ≤
        (selectedSum points j k 0 negative (selected j k negative))^2 ∧
      (NICertificate.halfRoot^2*‖points k-points j‖^2 <
        (selectedSum points j k 0 negative (selected j k negative))^2 ∨
        ∃i,points (selected j k negative i)=0))
    (T : UnitTriangle) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0:Plane) r ⊆ T.region) (contained : ∀j,points j∈T.region) : False :=
  cannot_contain_with_origin_ball points hinj hjk (certificate points selected checked)
    T hr hball contained

end
end HexagonCover.ContinuousSupportWeak
