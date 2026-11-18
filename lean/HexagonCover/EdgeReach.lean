import HexagonCover.Geometry

/-! Actual edge reaches, tied to one actual triangle and two fixed endpoints.
The reach is an attained maximum, with all contact/equality cases retained. -/
namespace HexagonCover.EdgeReach
open AffineMap
noncomputable section

def parameters (T : UnitTriangle) (u v : Plane) : Set ℝ :=
  Set.Icc 0 1 ∩ (lineMap u v) ⁻¹' T.region

theorem parameters_compact (T : UnitTriangle) (u v : Plane) :
    IsCompact (parameters T u v) :=
  isCompact_Icc.inter_right
    (T.closed_region.preimage (lipschitzWith_lineMap (𝕜 := ℝ) u v).continuous)

theorem parameters_convex (T : UnitTriangle) (u v : Plane) :
    Convex ℝ (parameters T u v) :=
  (convex_Icc (0 : ℝ) 1).inter ((T.convex_region).affine_preimage (lineMap u v))

theorem far_endpoint_excluded (T : UnitTriangle) (u v : Plane)
    (unit : dist u v = 1) {r : ℝ} (hr : 0 < r)
    (ball : Metric.ball u r ⊆ T.region) : v ∉ T.region := by
  let w := lineMap u v (-(r/2))
  have hw : w ∈ T.region := by
    apply ball
    change dist w u < r
    dsimp only [w]
    rw [dist_lineMap_left, unit]
    simp only [Real.norm_eq_abs, abs_neg, mul_one]
    rw [abs_of_pos (by linarith : 0 < r/2)]
    linarith
  intro hv
  have hd := T.dist_le_one hw hv
  dsimp only [w] at hd
  rw [dist_lineMap_right, unit, mul_one, Real.norm_eq_abs] at hd
  rw [abs_of_pos (by linarith : 0 < 1 - -(r/2))] at hd
  linarith

structure Reach (T : UnitTriangle) (u v : Plane) where
  length : ℝ
  positive : 0 < length
  lt_one : length < 1
  endpoint : lineMap u v length ∈ T.region
  character : ∀ t ∈ Set.Icc (0 : ℝ) 1, lineMap u v t ∈ T.region ↔ t ≤ length

theorem exists_reach (T : UnitTriangle) (u v : Plane)
    (unit : dist u v = 1) {r : ℝ} (hr : 0 < r)
    (ball : Metric.ball u r ⊆ T.region) : Nonempty (Reach T u v) := by
  have hu : u ∈ T.region := ball (Metric.mem_ball_self hr)
  have hz : (0 : ℝ) ∈ parameters T u v := by
    exact ⟨by norm_num, by simpa only [Set.mem_preimage, lineMap_apply_zero] using hu⟩
  obtain ⟨a, ha, hmax⟩ := (parameters_compact T u v).exists_isGreatest ⟨0, hz⟩
  let ε : ℝ := min (r/2) (1/2)
  have hepos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hel : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have her : ε < r := (min_le_left _ _).trans_lt (by linarith)
  have hemem : ε ∈ parameters T u v := by
    refine ⟨⟨hepos.le, hel⟩, ?_⟩
    apply ball
    change dist (lineMap u v ε) u < r
    rw [dist_lineMap_left, unit, mul_one, Real.norm_eq_abs, abs_of_pos hepos]
    exact her
  have hapos : 0 < a := hepos.trans_le (hmax hemem)
  have haone : a < 1 := by
    apply lt_of_le_of_ne ha.1.2
    intro heq
    have hv : v ∈ T.region := by simpa [heq, parameters] using ha.2
    exact far_endpoint_excluded T u v unit hr ball hv
  refine ⟨⟨a, hapos, haone, ha.2, ?_⟩⟩
  intro t ht
  constructor
  · intro hpoint
    exact hmax ⟨ht, hpoint⟩
  · intro hta
    have hm := (parameters_convex T u v).ordConnected.out hz ha (show t ∈ Set.Icc 0 a from ⟨ht.1, hta⟩)
    exact hm.2

theorem length_unique {T : UnitTriangle} {u v : Plane} (a b : Reach T u v) :
    a.length = b.length := by
  apply le_antisymm
  · exact (b.character a.length ⟨a.positive.le, a.lt_one.le⟩).mp a.endpoint
  · exact (a.character b.length ⟨b.positive.le, b.lt_one.le⟩).mp b.endpoint

end
end HexagonCover.EdgeReach
