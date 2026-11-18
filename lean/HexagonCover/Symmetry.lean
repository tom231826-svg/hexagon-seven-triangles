import HexagonCover.RigidMotion
import HexagonCover.CornerChart

/-! Global geometric symmetries act on every actual piece. These results never
combine properties taken from different hypothetical configurations. -/
namespace HexagonCover.Symmetry
noncomputable section

def mapTriangle (f : Plane ≃ᵃⁱ[ℝ] Plane) (T : UnitTriangle) : UnitTriangle where
  vertex i := f (T.vertex i)
  edgeLength i j hij := by rw [f.isometry.dist_eq]; exact T.edgeLength i j hij

theorem map_region (f : Plane ≃ᵃⁱ[ℝ] Plane) (T : UnitTriangle) :
    (mapTriangle f T).region = f '' T.region := by
  have h := f.toAffineEquiv.toAffineMap.image_convexHull (Set.range T.vertex)
  change f '' T.region = convexHull ℝ (f '' Set.range T.vertex) at h
  rw [← Set.range_comp] at h
  exact h.symm

theorem map_cover {s : ℝ} (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (hhex : f '' Hexagon s = Hexagon s) (config : Fin 7 → UnitTriangle)
    (covered : Covers s config) : Covers s (fun i => mapTriangle f (config i)) := by
  intro p hp
  rw [← hhex] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (covered hq)
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [map_region]
  exact ⟨q, hi, rfl⟩

def turn : Plane ≃ᵃⁱ[ℝ] Plane :=
  (RigidMotion.rotationIsometry (1/2) NICertificate.halfRoot
    (by nlinarith [ExtremeTriangle.halfRoot_sq])).toAffineIsometryEquiv

theorem turn_apply (p : Plane) : turn p =
    point ((1/2)*p 0-NICertificate.halfRoot*p 1)
      (NICertificate.halfRoot*p 0+(1/2)*p 1) := rfl

theorem turn_zero : turn 0 = 0 := by simp [turn_apply]

theorem turn_norm (p : Plane) : ‖turn p‖ = ‖p‖ := by
  simpa only [turn_zero, dist_zero_right] using turn.isometry.dist_eq p 0

theorem turn_vertex (s : ℝ) (i : Fin 6) : turn (hexVertex s i) = hexVertex s (i+1) := by
  rw [turn_apply]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [hexVertex, NICertificate.halfRoot, point]
  all_goals nlinarith [(congrArg (fun x : ℝ => x*s) (Real.sq_sqrt (by norm_num : (0:ℝ)≤3)))]

theorem turn_hexagon (s : ℝ) : turn '' Hexagon s = Hexagon s := by
  have hr : turn '' Set.range (hexVertex s) = Set.range (hexVertex s) := by
    ext p
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i+1, (turn_vertex s i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨hexVertex s (i-1), ⟨i-1, rfl⟩, ?_⟩
      simpa only [sub_add_cancel] using turn_vertex s (i-1)
  have h := turn.toAffineEquiv.toAffineMap.image_convexHull (Set.range (hexVertex s))
  change turn '' Hexagon s = convexHull ℝ (turn '' Set.range (hexVertex s)) at h
  rw [hr] at h
  exact h

def NonIntruding (radius : ℝ) (T : UnitTriangle) : Prop :=
  ∀ p ∈ T.region, radius ≤ ‖p‖

theorem turn_nonintruding {radius : ℝ} {T : UnitTriangle} (h : NonIntruding radius T) :
    NonIntruding radius (mapTriangle turn T) := by
  intro p hp
  rw [map_region] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [turn_norm]
  exact h q hq

theorem reflect_norm (p : Plane) : ‖CornerChart.reflect p‖ = ‖p‖ := by
  have h := CornerChart.reflection_dist p 0
  simpa [CornerChart.reflect] using h

theorem reflect_nonintruding {radius : ℝ} {T : UnitTriangle} (h : NonIntruding radius T) :
    NonIntruding radius (CornerChart.reflectedTriangle T) := by
  intro p hp
  rw [CornerChart.reflectedTriangle_region] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [reflect_norm]
  exact h q hq

theorem reflect_cover (config : Fin 7 → UnitTriangle) (covered : Covers 1 config) :
    Covers 1 (fun i => CornerChart.reflectedTriangle (config i)) := by
  intro p hp
  have hr : CornerChart.reflect p ∈ Hexagon 1 := by
    rw [← CornerChart.reflection_hexagon]
    exact ⟨p, hp, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (covered hr)
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [CornerChart.reflectedTriangle_region]
  exact ⟨CornerChart.reflect p, hi, CornerChart.reflect_reflect p⟩

end
end HexagonCover.Symmetry
