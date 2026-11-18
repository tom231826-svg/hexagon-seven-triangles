import HexagonCover.CornerTransport

/-! Reach-cost bookkeeping on one actual StrictCover. The universal reach
lower bound is explicit here and remains a separate geometric obligation. -/
namespace HexagonCover.ReachBudget
open HexagonCover.Configuration MeasureTheory
open scoped Classical
noncomputable section

def heavy {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) : Prop :=
  1 ≤ a h i + b h i

def cost {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) : ℝ :=
  if heavy h i then (max (a h i) (b h i))^2 else (min (a h i) (b h i))^2

theorem min_pos {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    0 < min (a h i) (b h i) :=
  lt_min (leftReach h i).positive (rightReach h i).positive

theorem min_square_le_cost {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) : (min (a h i) (b h i))^2 ≤ cost h i := by
  unfold cost
  split_ifs
  · exact pow_le_pow_left₀ (min_pos h i).le min_le_max 2
  · rfl

theorem cost_loss_bound {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) :
    AreaCorollaries.delta * cost h i ≤ volume.real ((config i.castSucc).region \ Hexagon 1) := by
  unfold cost
  split_ifs with hi
  · exact (CornerTransport.actual_reach_loss h i).2 hi
  · exact (CornerTransport.actual_reach_loss h i).1

theorem cost_budget {config : Fin 7 → UnitTriangle} (h : StrictCover config) :
    ∑ i : Fin 6, cost h i ≤ 1 := by
  have hb := AreaCorollaries.unit_cover_exterior_budget config h.covered
  rw [Fin.sum_univ_castSucc] at hb
  change (∑ i : Fin 6, volume.real ((config i.castSucc).region \ Hexagon 1)) +
    volume.real ((config 6).region \ Hexagon 1) ≤ AreaCorollaries.delta at hb
  have hc : 0 ≤ volume.real ((config 6).region \ Hexagon 1) := ENNReal.toReal_nonneg
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 6) _ => cost_loss_bound h i)
  rw [← Finset.mul_sum] at hs
  apply (mul_le_mul_iff_right₀ AreaCorollaries.delta_pos).mp
  linarith

theorem heavy_max_half {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hi : heavy h i) :
    (1:ℝ)/2 ≤ max (a h i) (b h i) := by
  have ha := le_max_left (a h i) (b h i)
  have hb := le_max_right (a h i) (b h i)
  change 1 ≤ a h i + b h i at hi
  linarith

theorem heavy_cost_quarter {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hi : heavy h i) : (1:ℝ)/4 ≤ cost h i := by
  rw [cost, if_pos hi]
  nlinarith [heavy_max_half h i hi]

/-- The source's area contradiction for a second heavy outer piece. The reach
lower bound must first be obtained from the same actual configuration. -/
theorem unique_heavy_of_reach_lower {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (j : Fin 6) (hj : heavy h j)
    (lower : ∀ i, 1 - max (a h j) (b h j) ≤ min (a h i) (b h i)) :
    ∀ k, heavy h k → k = j := by
  let M := max (a h j) (b h j)
  let t := 1-M
  have hMlt : M < 1 := max_lt (leftReach h j).lt_one (rightReach h j).lt_one
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hsq (i : Fin 6) : t^2 ≤ cost h i :=
    (pow_le_pow_left₀ ht (lower i) 2).trans (min_square_le_cost h i)
  have hjcost : cost h j = M^2 := by simp only [cost, if_pos hj, M]
  intro k hk
  by_contra hkj
  let base (i : Fin 6) : ℝ := t^2 +
    (if i=j then M^2-t^2 else 0) + (if i=k then (1:ℝ)/4-t^2 else 0)
  have hb (i : Fin 6) : base i ≤ cost h i := by
    by_cases hij : i=j
    · subst i
      have hjk : j ≠ k := Ne.symm hkj
      simp only [base, eq_self, ite_true, if_neg hjk]
      linarith
    · by_cases hik : i=k
      · subst i
        simp only [base, eq_self, if_neg hkj, ite_true]
        linarith [heavy_cost_quarter h k hk]
      · simp only [base, if_neg hij, if_neg hik, add_zero]
        exact hsq i
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 6) _ => hb i)
  have he : (∑ i : Fin 6, base i) = M^2 + (1:ℝ)/4 + 4*t^2 := by
    simp [base, Finset.sum_add_distrib]
    ring
  rw [he] at hsum
  have hbudget := cost_budget h
  dsimp only [t] at hsum
  nlinarith [sq_nonneg (M-(4:ℝ)/5)]

end
end HexagonCover.ReachBudget
