import HexagonCover.TriangleArea
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Lebesgue area of arbitrary closed planar triangles, including degenerate
ones. The proof uses a linear image of the measured standard triangle; the
Haar determinant theorem itself handles singular maps. -/

namespace HexagonCover.TriangleMeasure

noncomputable section

open MeasureTheory MeasureTheory.Measure RigidMotion

def det (p q : Plane) : ℝ := p 0 * q 1 - p 1 * q 0

def triangle (p q r : Plane) : Set Plane := convexHull ℝ (Set.range ![p, q, r])

theorem triangle_eq_convexHull (p q r : Plane) :
    triangle p q r = convexHull ℝ ({p, q, r} : Set Plane) := by
  unfold triangle
  congr 1
  ext z
  simp [Fin.exists_fin_succ]
  tauto

theorem triangle_compact (p q r : Plane) : IsCompact (triangle p q r) :=
  (Set.finite_range ![p, q, r]).isCompact_convexHull ℝ

theorem triangle_convex (p q r : Plane) : Convex ℝ (triangle p q r) :=
  convex_convexHull ℝ _

theorem triangle_subset_of_convex {s : Set Plane} (hs : Convex ℝ s)
    {p q r : Plane} (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s) : triangle p q r ⊆ s := by
  apply convexHull_min _ hs
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

theorem image_triangle (f : Plane →ᵃ[ℝ] Plane) (p q r : Plane) :
    f '' triangle p q r = triangle (f p) (f q) (f r) := by
  unfold triangle
  rw [f.image_convexHull, ← Set.range_comp]
  congr 1
  congr 1
  funext i
  fin_cases i <;> rfl

def columnMap (p q : Plane) : Plane →ₗ[ℝ] Plane where
  toFun z := z 0 • p + z 1 • q
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

theorem columnMap_det (p q : Plane) : LinearMap.det (columnMap p q) = det p q := by
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (columnMap p q) =
      !![p 0, q 0; p 1, q 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, columnMap]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, hm]
  simp [Matrix.det_fin_two, det]
  ring

def standardMap (p q : Plane) : Plane →ₗ[ℝ] Plane :=
  columnMap p (NICertificate.halfRoot⁻¹ • (q - (1 / 2 : ℝ) • p))

theorem standardMap_vertices (p q : Plane) (i : Fin 3) :
    standardMap p q (standardVertices i) = (![0, p, q] : Fin 3 → Plane) i := by
  have hh : NICertificate.halfRoot ≠ 0 := ne_of_gt ExtremeTriangle.halfRoot_pos
  fin_cases i <;> ext j <;> fin_cases j
  all_goals simp [standardMap, columnMap, standardVertices]
  all_goals field_simp [hh]
  all_goals ring

theorem standardMap_image (p q : Plane) :
    standardMap p q '' standardRegion = triangle 0 p q := by
  change standardMap p q '' convexHull ℝ (Set.range standardVertices) = _
  rw [(standardMap p q).image_convexHull, ← Set.range_comp]
  unfold triangle
  congr 1
  congr 1
  exact funext (standardMap_vertices p q)

theorem standardMap_det (p q : Plane) :
    LinearMap.det (standardMap p q) = det p q / NICertificate.halfRoot := by
  rw [standardMap, columnMap_det]
  simp [det, div_eq_mul_inv]
  ring

theorem standardRegion_area : volume.real standardRegion = Real.sqrt 3 / 4 := by
  rw [← TriangleArea.standard_closedInterior,
    ← Affine.Simplex.volume_eq_volume_real_closedInterior
      (finrank_euclideanSpace_fin (𝕜 := ℝ)) TriangleArea.standardSimplex]
  exact TriangleArea.standard_simplex_volume

/-- The determinant formula is valid even when the points are collinear. -/
theorem origin_triangle_area (p q : Plane) :
    volume.real (triangle 0 p q) = |det p q| / 2 := by
  rw [← standardMap_image, measureReal_def, addHaar_image_linearMap,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  change |LinearMap.det (standardMap p q)| * volume.real standardRegion = _
  rw [standardMap_det, abs_div, abs_of_pos ExtremeTriangle.halfRoot_pos,
    standardRegion_area]
  unfold NICertificate.halfRoot
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
  ring

theorem translation_area (p : Plane) (s : Set Plane) :
    volume.real ((fun z => p + z) '' s) = volume.real s := by
  unfold Measure.real
  rw [Set.image_add_left, measure_preimage_add]

theorem triangle_translation (p q r : Plane) :
    (fun z => p + z) '' triangle 0 (q - p) (r - p) = triangle p q r := by
  have h := image_triangle (AffineEquiv.constVAdd ℝ Plane p).toAffineMap 0 (q - p) (r - p)
  simpa using h

/-- Actual Lebesgue area of any closed triangle in the physical Euclidean plane. -/
theorem triangle_area (p q r : Plane) :
    volume.real (triangle p q r) = |det (q - p) (r - p)| / 2 := by
  rw [← triangle_translation, translation_area, origin_triangle_area]

end
end HexagonCover.TriangleMeasure
