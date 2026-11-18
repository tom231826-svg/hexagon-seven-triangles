import HexagonCover.AreaBudget
import HexagonCover.TriangleArea
import HexagonCover.HexagonArea
import HexagonCover.Normalization

/-! Numerical area bounds discharged against actual planar Lebesgue measure.
Loss outside H1 and loss outside Hs are distinct quantities. -/
namespace HexagonCover.AreaCorollaries
open scoped BigOperators
open AreaBudget
noncomputable section

def delta : ℝ := Real.sqrt 3 / 4

theorem delta_pos : 0 < delta := by unfold delta; positivity

theorem unit_area (T : UnitTriangle) : area T.region = delta :=
  TriangleArea.unitTriangle_area T

theorem hex_area (s : ℝ) : area (Hexagon s) = 6 * s^2 * delta := by
  rw [area, HexagonArea.hexagon_area]
  unfold delta
  ring

theorem normalized_exterior_budget {s : ℝ} (config : Fin 7 → UnitTriangle)
    (covered : Covers s config) :
    (∑ i, area ((config i).region \ Hexagon s)) / delta ≤ 7 - 6 * s^2 :=
  AreaBudget.normalized_loss_bound delta_pos config covered
    (fun i => unit_area (config i)) (hex_area s)

theorem area_restriction {s : ℝ} (config : Fin 7 → UnitTriangle)
    (covered : Covers s config) : 6 * s^2 ≤ 7 := by
  have hn : (0 : ℝ) ≤ (∑ i, area ((config i).region \ Hexagon s)) / delta := by
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro i _
      exact ENNReal.toReal_nonneg
    · exact delta_pos.le
  have hb := normalized_exterior_budget config covered
  linarith

theorem unit_cover_exterior_budget (config : Fin 7 → UnitTriangle)
    (covered : Covers 1 config) :
    (∑ i, area ((config i).region \ Hexagon 1)) ≤ delta := by
  have hb := normalized_exterior_budget config covered
  norm_num only [one_pow, mul_one, sub_self, sub_zero, show (7:ℝ)-6=1 by norm_num] at hb
  have hm := (div_le_iff₀ delta_pos).mp hb
  simpa using hm

theorem expanded_cover_H1_budget {s : ℝ} (hs : 1 < s)
    (config : Fin 7 → UnitTriangle) (covered : Covers s config) :
    (∑ i, area ((config i).region \ Hexagon 1)) ≤ delta :=
  unit_cover_exterior_budget config
    (Normalization.covers_one_of_expanded_cover hs config covered)

theorem expanded_cover_Hs_strict_budget {s : ℝ} (hs : 1 < s)
    (config : Fin 7 → UnitTriangle) (covered : Covers s config) :
    (∑ i, area ((config i).region \ Hexagon s)) < delta := by
  have hb := normalized_exterior_budget config covered
  have hr : 7 - 6 * s^2 < (1:ℝ) := by nlinarith
  have hm := (div_lt_iff₀ delta_pos).mp (hb.trans_lt hr)
  simpa using hm

end
end HexagonCover.AreaCorollaries
