import HexagonCover.E4InsideForced
import HexagonCover.CentralAxis
import HexagonCover.ContinuousSupportWeak
import HexagonCover.PaSupportArithmetic

/-! Source-exposed same-C moving-point exclusion for sole E4. The imported
Pa packet uses the mandatory D--O sign erratum. Unit equality is preserved;
the actual strict central origin, not a rounded strict size bound, excludes it.
This is a common lemma before the A-in-closed-T2 owner split. -/
namespace HexagonCover.E4InsideCentral
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

def Pa (a : ℝ) : Plane := point 0 (-h₀*a)

theorem packet_injective {a : ℝ} (ha : 0 < a) (ha1 : a < 4/25) :
    Function.Injective (PaSupportArithmetic.points a) := by
  intro i j hij
  have hx := congrArg (fun p : Plane => p 0) hij
  have hy := congrArg (fun p : Plane => p 1) hij
  have hprod := mul_pos ExtremeTriangle.halfRoot_pos ha
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (simp only [PaSupportArithmetic.points,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val,Matrix.head_cons,Fin.reduceFinMk,
        point_coord_zero,point_coord_one] at hx hy
       exfalso
       nlinarith [ExtremeTriangle.halfRoot_pos])

/-- Every real orientation, including the unique unit-equality event, is
handled by the geometric support-event completeness theorem. -/
theorem excluded_of_duties (T : UnitTriangle) {a r : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hr : 0 < r)
    (hball : Metric.ball (0:Plane) r ⊆ T.region)
    (hD : E4InsideForced.D∈T.region) (hP : CentralAxis.P a∈T.region) :
    Pa a∉T.region := by
  intro hPa
  apply ContinuousSupportWeak.impossible (PaSupportArithmetic.points a)
    (packet_injective ha ha1) (show (0:Fin 4)≠1 by decide)
    PaSupportArithmetic.selected (PaSupportArithmetic.checked ha ha1) T hr hball
  intro j
  fin_cases j
  · simpa [PaSupportArithmetic.points] using hball (Metric.mem_ball_self hr)
  · exact hD
  · have he : CentralAxis.P a=point (1-a/2) (-h₀*a) := by
      ext i
      fin_cases i <;> simp [CentralAxis.P,ExteriorLoss.lowerEndpoint,
        ExteriorLoss.corner,ExteriorLoss.lowerRay] <;> ring
    rw [he] at hP
    exact hP
  · exact hPa

theorem actual_a_bounds {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) :
    0 < a h.cover 5 ∧ a h.cover 5 < 4/25 := by
  have hM := GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩
  exact ⟨(leftReach h.cover 5).positive,by linarith [GapChains.heavy_short h]⟩

/-- Actual sole-E4 Pa is outside the same actual closed central triangle. -/
theorem actual_excluded {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) :
    Pa (a h.cover 5)∉(rotateConfig config 6).region := by
  obtain ⟨ha,ha1⟩ := actual_a_bounds h sole
  obtain ⟨r,hr,hb⟩ := h.cover.anchorBalls (6:Fin 7)
  rw [qAnchor_center] at hb
  have hrot := CornerTransport.action_ball QSymmetry.rotationAction (config 6) 0 hb
  change Metric.ball (Symmetry.turn 0) r ⊆ (rotateConfig config 6).region at hrot
  rw [Symmetry.turn_zero] at hrot
  exact excluded_of_duties _ ha ha1 hr hrot (E4InsideForced.same_central h sole)
    (CentralAxis.source_P_mem h ((sole 4).mpr rfl))

#print axioms actual_excluded

end
end HexagonCover.E4InsideCentral
