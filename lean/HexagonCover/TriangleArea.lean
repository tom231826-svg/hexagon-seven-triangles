import HexagonCover.RigidMotion
import Mathlib.Geometry.Euclidean.Volume.Basic

/-! Exact Lebesgue area of every actual unit equilateral triangle. -/

namespace HexagonCover.TriangleArea

noncomputable section

open RigidMotion MeasureTheory EuclideanGeometry

private theorem standard_independent : AffineIndependent ℝ standardVertices := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hV i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hw] at hV
  have hx := congrArg (fun p : Plane => p 0) hV
  have hy := congrArg (fun p : Plane => p 1) hV
  simp [Fin.sum_univ_three, standardVertices] at hx hy hw
  have hh : NICertificate.halfRoot ≠ 0 := ne_of_gt ExtremeTriangle.halfRoot_pos
  have h2 : w 2 = 0 := hy.resolve_right hh
  have h1 : w 1 = 0 := by rw [h2] at hx; linarith
  have h0 : w 0 = 0 := by rw [h1, h2] at hw; linarith
  fin_cases i <;> assumption

def standardSimplex : Affine.Simplex ℝ Plane 2 := ⟨standardVertices, standard_independent⟩

theorem standard_closedInterior : standardSimplex.closedInterior = standardRegion :=
  (Affine.Simplex.convexHull_eq_closedInterior standardSimplex).symm

private theorem standard_base_range :
    Set.range (standardSimplex.faceOpposite 2).points = {0, point 1 0} := by
  rw [Affine.Simplex.range_faceOpposite_points]
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all [standardSimplex, standardVertices]
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩

private theorem standard_base_span :
    affineSpan ℝ (Set.range (standardSimplex.faceOpposite 2).points) =
      (Submodule.span ℝ {point 1 0}).toAffineSubspace := by
  rw [standard_base_range, affineSpan_insert_zero]

private theorem standard_altitude_foot :
    standardSimplex.altitudeFoot 2 = point (1 / 2) 0 := by
  unfold Affine.Simplex.altitudeFoot Affine.Simplex.orthogonalProjectionSpan
  apply coe_orthogonalProjection_eq_iff_mem.mpr
  constructor
  · rw [standard_base_span]
    change point (1 / 2) 0 ∈ Submodule.span ℝ {point 1 0}
    apply Submodule.mem_span_singleton.mpr
    refine ⟨1 / 2, ?_⟩
    ext i
    fin_cases i <;> norm_num [point]
  · rw [standard_base_span, Submodule.toAffineSubspace_direction,
      Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [standardSimplex, standardVertices, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two, point]

theorem standard_height : standardSimplex.height 2 = NICertificate.halfRoot := by
  rw [Affine.Simplex.height, standard_altitude_foot]
  change dist (point (1 / 2) NICertificate.halfRoot) (point (1 / 2) 0) = NICertificate.halfRoot
  have hd := dist_point_sq (1 / 2) NICertificate.halfRoot (1 / 2) 0
  have hn : 0 ≤ dist (point (1 / 2) NICertificate.halfRoot) (point (1 / 2) 0) := dist_nonneg
  nlinarith [ExtremeTriangle.halfRoot_pos]

theorem standard_base_volume : (standardSimplex.faceOpposite 2).volume = 1 := by
  rw [Affine.Simplex.volume_eq_dist]
  have h0 : (standardSimplex.faceOpposite 2).points 0 = 0 := by
    rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove]
    rfl
  have h1 : (standardSimplex.faceOpposite 2).points 1 = point 1 0 := by
    rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove]
    rfl
  rw [h0, h1]
  norm_num [dist_eq_norm, EuclideanSpace.norm_eq, point, Fin.sum_univ_two]

theorem standard_simplex_volume : standardSimplex.volume = Real.sqrt 3 / 4 := by
  rw [Affine.Simplex.volume_eq standardSimplex 2, standard_height, standard_base_volume]
  norm_num [NICertificate.halfRoot]
  ring

/-- This is Lebesgue area of the full closed triangle, including its boundary. -/
theorem unitTriangle_area (T : UnitTriangle) :
    MeasureTheory.volume.real T.region = Real.sqrt 3 / 4 := by
  obtain ⟨a, c, d, hu, hT⟩ := exists_region_rigid_motion T
  let f := rigid a c d hu
  let F : Plane →ᵃ[ℝ] Plane := f.toAffineEquiv.toAffineMap
  have hF : Function.Injective F := f.injective
  let S := standardSimplex.map F hF
  have hregion : S.closedInterior = T.region := by
    calc
      S.closedInterior = F '' standardSimplex.closedInterior :=
        standardSimplex.closedInterior_map hF
      _ = F '' standardRegion := by rw [standard_closedInterior]
      _ = T.region := hT.symm
  rw [← hregion, ← Affine.Simplex.volume_eq_volume_real_closedInterior
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) S]
  have hv : S.volume = standardSimplex.volume :=
    Affine.Simplex.volume_map standardSimplex f.toAffineIsometry
  exact hv.trans standard_simplex_volume

end
end HexagonCover.TriangleArea
