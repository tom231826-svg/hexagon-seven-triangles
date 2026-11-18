import HexagonCover.Geometry

/-! Actual planar Lebesgue area accounting. The accounting lemma does not
assume disjoint pieces; overlaps only weaken the bound. Numerical triangle and
hexagon area formulas must be supplied separately and are not axioms here. -/

namespace HexagonCover.AreaBudget
open MeasureTheory
open scoped BigOperators
noncomputable section

def area (s : Set Plane) : ℝ := volume.real s

theorem covering_loss_budget {ι : Type*} [Fintype ι]
    (pieces : ι → Set Plane) (target : Set Plane)
    (hfinite : ∀ i, volume (pieces i) ≠ ⊤)
    (hmeasurable : MeasurableSet target)
    (hcover : target ⊆ ⋃ i, pieces i) :
    (∑ i, area (pieces i \ target)) + area target ≤ ∑ i, area (pieces i) := by
  have hdecomp : (∑ i, area (pieces i ∩ target)) +
      (∑ i, area (pieces i \ target)) = ∑ i, area (pieces i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact measureReal_inter_add_sdiff hmeasurable (hfinite i)
  have hunion : (⋃ i, pieces i ∩ target) = target := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact hi.2
    · intro hx
      rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hi, hx⟩
  have hbound := measureReal_iUnion_fintype_le (μ := volume) (fun i => pieces i ∩ target)
  rw [hunion] at hbound
  change area target ≤ ∑ i, area (pieces i ∩ target) at hbound
  linarith

theorem hexagon_measurable (s : ℝ) : MeasurableSet (Hexagon s) :=
  (Set.finite_range (hexVertex s)).isCompact_convexHull ℝ |>.isClosed.measurableSet

theorem actual_covering_loss_budget {s : ℝ} (config : Fin 7 → UnitTriangle)
    (hcover : Covers s config) :
    (∑ i, area ((config i).region \ Hexagon s)) + area (Hexagon s) ≤
      ∑ i, area (config i).region := by
  apply covering_loss_budget (fun i => (config i).region) (Hexagon s)
  · intro i
    exact (config i).compact_region.measure_ne_top
  · exact hexagon_measurable s
  · exact hcover

theorem normalized_loss_bound {s Δ : ℝ} (hΔ : 0 < Δ)
    (config : Fin 7 → UnitTriangle) (hcover : Covers s config)
    (hunit : ∀ i, area (config i).region = Δ)
    (hhex : area (Hexagon s) = 6 * s ^ 2 * Δ) :
    (∑ i, area ((config i).region \ Hexagon s)) / Δ ≤ 7 - 6 * s ^ 2 := by
  have h := actual_covering_loss_budget config hcover
  simp_rw [hunit] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [hhex] at h
  norm_num only [Nat.cast_ofNat] at h
  apply (div_le_iff₀ hΔ).mpr
  nlinarith

end
end HexagonCover.AreaBudget
