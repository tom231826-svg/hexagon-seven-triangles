import HexagonCover.GapForcedPoint
import HexagonCover.SourceGap

/-! The actual R--P(a) chord forces an interior positive horizontal axis segment.
The proof keeps R, P and the origin in one and the same central triangle. -/
namespace HexagonCover.CentralAxis
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
local notation "h₀" => NICertificate.halfRoot

def P (a : ℝ) : Plane := ExteriorLoss.lowerEndpoint a
def axisExit (a : ℝ) : ℝ := (1+22*a/5)/(1+7*a)

theorem chord_axis (T : UnitTriangle) {a : ℝ} (ha : 0 ≤ a)
    (hR : GapForcedPoint.R∈T.region) (hP : P a∈T.region) :
    point (axisExit a) 0∈T.region := by
  have hd : 0 < 1+7*a := by linarith
  have hsum : 7*a/(1+7*a)+1/(1+7*a)=1 := by
    field_simp [ne_of_gt hd]
    <;> ring
  have hm := T.convex_region hR hP
    (div_nonneg (by positivity) hd.le) (div_nonneg (by norm_num) hd.le) hsum
  have he : (7*a/(1+7*a)) • GapForcedPoint.R+(1/(1+7*a)) • P a=
      point (axisExit a) 0 := by
    ext i
    fin_cases i
    all_goals simp [GapForcedPoint.R,P,ExteriorLoss.lowerEndpoint,ExteriorLoss.corner,
      ExteriorLoss.lowerRay,axisExit]
    all_goals field_simp [ne_of_gt hd] <;> ring
  exact he ▸ hm

theorem exit_gt {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1/5) : 47/60 < axisExit a := by
  have hd : 0 < 1+7*a := by linarith
  unfold axisExit
  apply (lt_div_iff₀ hd).mpr
  linarith

/-- Actual geometric core: no central orientation or support-chart premise.
Even closed R membership suffices because the origin supplies positive interior weight. -/
theorem axis_of_points (T : UnitTriangle) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1/5)
    (hO : (0:Plane)∈interior T.region)
    (hR : GapForcedPoint.R∈T.region) (hP : P a∈T.region) :
    ∀x∈Set.Icc (0:ℝ) (47/60),point x 0∈interior T.region := by
  have hXmem := chord_axis T ha hR hP
  have hX := exit_gt ha ha1
  have hX0 : 0 < axisExit a := by linarith
  intro x hx
  have hxX : x/axisExit a < 1 := (div_lt_one hX0).mpr (hx.2.trans_lt hX)
  have hb : 0 ≤ x/axisExit a := div_nonneg hx.1 hX0.le
  have hm := T.convex_region.combo_interior_self_mem_interior hO hXmem
    (a:=1-x/axisExit a) (b:=x/axisExit a) (by linarith) hb (by ring)
  have he : (1-x/axisExit a) • (0:Plane)+(x/axisExit a) • point (axisExit a) 0=point x 0 := by
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt hX0] <;> ring
  exact he ▸ hm

theorem source_origin_interior {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    (0:Plane)∈interior (rotateConfig config 6).region := by
  obtain ⟨r,hr,hb⟩ := h.cover.anchorBalls (6:Fin 7)
  rw [qAnchor_center] at hb
  have hrot := CornerTransport.action_ball QSymmetry.rotationAction (config 6) 0 hb
  change Metric.ball (Symmetry.turn 0) r ⊆ (rotateConfig config 6).region at hrot
  rw [Symmetry.turn_zero] at hrot
  apply interior_mono hrot
  rw [Metric.isOpen_ball.interior_eq]
  exact Metric.mem_ball_self hr

theorem source_P_mem {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (gap4 : BoundaryGaps.gap h.cover 4) :
    P (a h.cover 5)∈(rotateConfig config 6).region := by
  have hp := SourceGap.left_endpoint h.cover 4 gap4
  change AffineMap.lineMap (vertex 5) (vertex 4) (a h.cover 5)∈
    (rotateConfig config 6).region at hp
  have he := HeavyDepthTransport.lower_lineMap (a h.cover 5)
  change P (a h.cover 5)=AffineMap.lineMap (vertex 5) (vertex 4) (a h.cover 5) at he
  rwa [←he] at hp

end
end HexagonCover.CentralAxis
