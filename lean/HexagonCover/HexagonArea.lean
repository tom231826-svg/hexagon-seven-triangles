import HexagonCover.TriangleArea
import HexagonCover.StandardCover
import HexagonCover.Anchors
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The actual Lebesgue area of the closed regular hexagon. Its six fan triangles
overlap only along three null lines, so their areas add exactly. -/

namespace HexagonCover.HexagonArea

noncomputable section

open MeasureTheory MeasureTheory.Measure StandardCover
open scoped Pointwise

def firstForm : Fin 6 → Fin 6 := ![1, 0, 3, 5, 2, 0]
def secondForm : Fin 6 → Fin 6 := ![2, 5, 1, 4, 3, 4]

def sector (k : Fin 6) : Set Plane :=
  {p | 0 ≤ forms p (firstForm k) ∧ 0 ≤ forms p (secondForm k)}

theorem sector_convex (k : Fin 6) : Convex ℝ (sector k) := by
  intro x hx y hy a b ha hb hab
  constructor
  · rw [forms_linear]
    exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · rw [forms_linear]
    exact add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)

theorem fan_subset_sector (k : Fin 6) : (fan k).region ⊆ sector k := by
  apply convexHull_min _ (sector_convex k)
  rintro _ ⟨i, rfl⟩
  fin_cases k <;> fin_cases i
  all_goals norm_num [fan, fanVertices, sector, firstForm, secondForm, forms,
    vertex_u, vertex_v, coordU, coordV, hexVertex, point]
  all_goals (field_simp [sqrt3_ne_zero]; norm_num)

def boundary : Set Plane :=
  {p | coordU p = 0 ∨ coordV p = 0 ∨ coordU p - coordV p = 0}

theorem sector_inter_subset_boundary {i j : Fin 6} (hij : i ≠ j) :
    sector i ∩ sector j ⊆ boundary := by
  intro p hp
  by_contra hn
  change ¬ (coordU p = 0 ∨ coordV p = 0 ∨ coordU p - coordV p = 0) at hn
  push Not at hn
  obtain ⟨hi, hj⟩ := hp
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [sector, firstForm, secondForm, forms] at hi hj
  all_goals first
    | exact hn.1 (by linarith [hi.1, hi.2, hj.1, hj.2])
    | exact hn.2.1 (by linarith [hi.1, hi.2, hj.1, hj.2])
    | exact hn.2.2 (by linarith [hi.1, hi.2, hj.1, hj.2])

def formLinear (i : Fin 6) : Plane →ₗ[ℝ] ℝ where
  toFun p := forms p i
  map_add' x y := by simpa using forms_linear x y 1 1 i
  map_smul' a p := by simpa using forms_linear p 0 a 0 i

theorem first_three_forms_nonzero (i : Fin 3) :
    formLinear (i.castAdd 3) (point 2 (Real.sqrt 3)) ≠ 0 := by
  fin_cases i <;> norm_num [formLinear, forms, coordU, coordV, point, sqrt3_ne_zero]

theorem boundary_null : volume boundary = 0 := by
  have hnull (i : Fin 3) : volume ((formLinear (i.castAdd 3)).ker : Set Plane) = 0 := by
    apply addHaar_submodule
    intro heq
    have hm : point 2 (Real.sqrt 3) ∈ (formLinear (i.castAdd 3)).ker := by
      rw [heq]
      trivial
    exact first_three_forms_nonzero i hm
  have hb : boundary = ⋃ i : Fin 3, ((formLinear (i.castAdd 3)).ker : Set Plane) := by
    ext p
    simp [boundary, formLinear, forms, Fin.exists_fin_succ]
  rw [hb]
  exact measure_iUnion_null hnull

theorem fans_aedisjoint : Pairwise (fun i j : Fin 6 => AEDisjoint (volume : Measure Plane) (fan i).region (fan j).region) := by
  intro i j hij
  apply measure_mono_null _ boundary_null
  exact (Set.inter_subset_inter (fan_subset_sector i) (fan_subset_sector j)).trans
    (sector_inter_subset_boundary hij)

theorem fan_subset_hexagon (k : Fin 6) : (fan k).region ⊆ Hexagon 1 := by
  apply convexHull_min _ (convex_hexagon 1)
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · change point 0 0 ∈ Hexagon 1
    rw [point_zero]
    exact interior_subset (zero_mem_interior_hexagon (s := 1) (by norm_num))
  · exact hexVertex_mem 1 k
  · exact hexVertex_mem 1 (k + 1)

theorem hexagon_eq_fans : Hexagon 1 = ⋃ k : Fin 6, (fan k).region := by
  apply Set.Subset.antisymm
  · intro p hp
    exact Set.mem_iUnion.mpr (six_fans_cover hp)
  · exact Set.iUnion_subset fan_subset_hexagon

theorem unit_hexagon_area : volume.real (Hexagon 1) = 3 * Real.sqrt 3 / 2 := by
  rw [hexagon_eq_fans, measureReal_def, measure_iUnion₀ fans_aedisjoint
    (fun k => (fan k).closed_region.measurableSet.nullMeasurableSet), tsum_fintype,
    ENNReal.toReal_sum (fun k _ => (fan k).compact_region.measure_ne_top)]
  change (∑ k : Fin 6, volume.real (fan k).region) = _
  simp_rw [TriangleArea.unitTriangle_area]
  norm_num
  ring

theorem hexagon_smul (s : ℝ) : Hexagon s = s • Hexagon 1 := by
  unfold Hexagon
  have hr : Set.range (hexVertex s) = s • Set.range (hexVertex 1) := by
    rw [show hexVertex s = (fun i => s • hexVertex 1 i) from funext (hexVertex_smul s)]
    exact Set.range_smul s (hexVertex 1)
  rw [hr, convexHull_smul]

/-- The formula applies to every real scale, and in particular to the problem's `s > 1`. -/
theorem hexagon_area (s : ℝ) :
    volume.real (Hexagon s) = 3 * Real.sqrt 3 / 2 * s ^ 2 := by
  rw [hexagon_smul, measureReal_def, addHaar_smul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  change |s ^ Module.finrank ℝ Plane| * volume.real (Hexagon 1) = _
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg s), unit_hexagon_area]
  ring

end
end HexagonCover.HexagonArea
