import HexagonCover.SupportGeometry

/-! Real-parameter selected-support obligations. Every inequality is a Lean
proof on the complete real parameter domain; candidate indices prove nothing. -/
namespace HexagonCover.ContinuousSupport
open TriangleFrame SupportGeometry
noncomputable section

def selectedSum {n : ℕ} (points : Fin (n+1) → Plane) (j k : Fin (n+1))
    (role : Fin 3) (negative : Bool) (selected : Fin 3 → Fin (n+1)) : ℝ :=
  branch points selected ((eventBase (points j) (points k) role negative) 0)
    ((eventBase (points j) (points k) role negative) 1)

theorem selected_le_total {n : ℕ} (points : Fin (n+1) → Plane) (j k : Fin (n+1))
    (role : Fin 3) (negative : Bool) (selected : Fin 3 → Fin (n+1)) :
    selectedSum points j k role negative selected ≤
      total points ((eventBase (points j) (points k) role negative) 0)
        ((eventBase (points j) (points k) role negative) 1) :=
  branch_le_total points selected _ _

theorem eventBound_of_squared {n : ℕ} (points : Fin (n+1) → Plane)
    (selected : Fin (n+1) → Fin (n+1) → Fin 3 → Bool → Fin 3 → Fin (n+1))
    (checked : ∀j k, j≠k → ∀role negative,
      0 < selectedSum points j k role negative (selected j k role negative) ∧
      NICertificate.halfRoot^2 * ‖points k-points j‖^2 <
        (selectedSum points j k role negative (selected j k role negative))^2) :
    EventBound points NICertificate.halfRoot := by
  intro j k hjk role negative
  have hij : j≠k := fun he=>hjk (congrArg points he)
  obtain ⟨hpos,hsq⟩ := checked j k hij role negative
  have hs : NICertificate.halfRoot*‖points k-points j‖ <
      selectedSum points j k role negative (selected j k role negative) := by
    apply (sq_lt_sq₀ (mul_nonneg ExtremeTriangle.halfRoot_pos.le (norm_nonneg _)) hpos.le).mp
    simpa only [mul_pow] using hsq
  exact hs.trans_le (selected_le_total points j k role negative _)

theorem impossible {n : ℕ} (points : Fin (n+1) → Plane)
    {j k : Fin (n+1)} (distinct : points j≠points k)
    (selected : Fin (n+1) → Fin (n+1) → Fin 3 → Bool → Fin 3 → Fin (n+1))
    (checked : ∀j k, j≠k → ∀role negative,
      0 < selectedSum points j k role negative (selected j k role negative) ∧
      NICertificate.halfRoot^2 * ‖points k-points j‖^2 <
        (selectedSum points j k role negative (selected j k role negative))^2)
    (T : UnitTriangle) (contained : ∀j,points j∈T.region) : False :=
  cannot_contain_of_eventBounds points distinct (eventBound_of_squared points selected checked) T contained

end
end HexagonCover.ContinuousSupport
