import HexagonCover.Geometry

/-! An explicit feasible boundary control: the unit hexagon is covered by its six fans. -/

namespace HexagonCover.StandardCover

noncomputable section

def height : ℝ := Real.sqrt 3 / 2

theorem sqrt3_pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
theorem sqrt3_ne_zero : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt sqrt3_pos

def fanVertices (k : Fin 6) : Fin 3 → Plane :=
  ![point 0 0, hexVertex 1 k, hexVertex 1 (k + 1)]

theorem fan_edge (k : Fin 6) (i j : Fin 3) (hij : i ≠ j) :
    dist (fanVertices k i) (fanVertices k j) = 1 := by
  have hroot : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : dist (fanVertices k i) (fanVertices k j) ^ 2 = 1 := by
    fin_cases k <;> fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals dsimp [fanVertices, hexVertex]
    all_goals rw [dist_point_sq]
    all_goals norm_num
    all_goals nlinarith
  have hn : 0 ≤ dist (fanVertices k i) (fanVertices k j) := dist_nonneg
  nlinarith

def fan (k : Fin 6) : UnitTriangle := ⟨fanVertices k, fan_edge k⟩

/-- Oblique coordinates for the triangular lattice. -/
def coordU (p : Plane) : ℝ := p 0 + p 1 / Real.sqrt 3
def coordV (p : Plane) : ℝ := 2 * p 1 / Real.sqrt 3

theorem vertex_u (k : Fin 6) : coordU (hexVertex 1 k) = ![1, 1, 0, -1, -1, 0] k := by
  fin_cases k <;> norm_num [coordU, hexVertex]
  all_goals field_simp [sqrt3_ne_zero]
  all_goals ring

theorem vertex_v (k : Fin 6) : coordV (hexVertex 1 k) = ![0, 1, 1, 0, -1, -1] k := by
  fin_cases k <;> norm_num [coordV, hexVertex]
  all_goals field_simp [sqrt3_ne_zero]

theorem reconstruct (p : Plane) :
    point (coordU p - coordV p / 2) (height * coordV p) = p := by
  ext i
  fin_cases i
  · simp [coordU, coordV, point]
    ring
  · simp [height, coordV, point]

def forms (p : Plane) : Fin 6 → ℝ :=
  ![coordU p, coordV p, coordU p - coordV p, -coordU p, -coordV p, coordV p - coordU p]

theorem forms_linear (x y : Plane) (a b : ℝ) (i : Fin 6) :
    forms (a • x + b • y) i = a * forms x i + b * forms y i := by
  fin_cases i <;> simp [forms, coordU, coordV] <;> ring

theorem hex_forms_bound {p : Plane} (hp : p ∈ Hexagon 1) (i : Fin 6) : forms p i ≤ 1 := by
  have hsub : Hexagon 1 ⊆ {p : Plane | ∀ i, forms p i ≤ 1} := by
    apply convexHull_min
    · rintro _ ⟨j, rfl⟩ i
      fin_cases i <;> fin_cases j <;> norm_num [forms, vertex_u, vertex_v]
    · intro x hx y hy a b ha hb hab i
      rw [forms_linear]
      have hx' := hx i
      have hy' := hy i
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'), mul_nonneg hb (sub_nonneg.mpr hy')]
  exact hsub hp i

theorem hex_coordinate_bounds {p : Plane} (hp : p ∈ Hexagon 1) :
    -1 ≤ coordU p ∧ coordU p ≤ 1 ∧ -1 ≤ coordV p ∧ coordV p ≤ 1 ∧
      -1 ≤ coordU p - coordV p ∧ coordU p - coordV p ≤ 1 := by
  have h0 := hex_forms_bound hp 0
  have h1 := hex_forms_bound hp 1
  have h2 := hex_forms_bound hp 2
  have h3 := hex_forms_bound hp 3
  have h4 := hex_forms_bound hp 4
  have h5 := hex_forms_bound hp 5
  norm_num [forms] at h0 h1 h2 h3 h4 h5
  exact ⟨by linarith, h0, by linarith, h1, by linarith, by linarith⟩

theorem fan_mem (k : Fin 6) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    a • hexVertex 1 k + b • hexVertex 1 (k + 1) ∈ (fan k).region := by
  apply mem_convexHull_of_exists_fintype ![1 - a - b, a, b] (fan k).vertex
  · intro i
    fin_cases i <;> norm_num <;> linarith
  · simp [Fin.sum_univ_three]
    ring
  · intro i
    exact ⟨i, rfl⟩
  · simp [fan, fanVertices, Fin.sum_univ_three]

theorem sector_zero (u v : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1) :
    point (u - v/2) (height * v) ∈ (fan 0).region := by
  have hm := fan_mem 0 (u - v) v (by linarith) hv (by linarith)
  convert hm using 1
  ext i
  fin_cases i <;> norm_num [hexVertex, point, height] <;> ring

theorem sector_one (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    point (u - v/2) (height * v) ∈ (fan 1).region := by
  have hm := fan_mem 1 u (v - u) hu (by linarith) (by linarith)
  convert hm using 1
  ext i
  fin_cases i <;> norm_num [hexVertex, point, height] <;> ring

theorem sector_two (u v : ℝ) (hu : u ≤ 0) (hv : 0 ≤ v) (hvu : v - u ≤ 1) :
    point (u - v/2) (height * v) ∈ (fan 2).region := by
  have hm := fan_mem 2 v (-u) hv (by linarith) (by linarith)
  convert hm using 1
  ext i
  fin_cases i <;> norm_num [hexVertex, point, height] <;> ring

theorem sector_three (u v : ℝ) (huv : u ≤ v) (hv : v ≤ 0) (hu : -1 ≤ u) :
    point (u - v/2) (height * v) ∈ (fan 3).region := by
  have hm := fan_mem 3 (v - u) (-v) (by linarith) (by linarith) (by linarith)
  convert hm using 1
  ext i
  fin_cases i <;> norm_num [hexVertex, point, height] <;> ring

theorem sector_four (u v : ℝ) (hvu : v ≤ u) (hu : u ≤ 0) (hv : -1 ≤ v) :
    point (u - v/2) (height * v) ∈ (fan 4).region := by
  have hm := fan_mem 4 (-u) (u - v) (by linarith) (by linarith) (by linarith)
  convert hm using 1
  ext i
  fin_cases i <;> norm_num [hexVertex, point, height] <;> ring

theorem sector_five (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ 0) (huv : u - v ≤ 1) :
    point (u - v/2) (height * v) ∈ (fan 5).region := by
  have hm := fan_mem 5 (-v) u (by linarith) hu (by linarith)
  convert hm using 1
  ext i
  fin_cases i <;> norm_num [hexVertex, point, height] <;> ring

theorem six_fans_cover {p : Plane} (hp : p ∈ Hexagon 1) :
    ∃ k : Fin 6, p ∈ (fan k).region := by
  obtain ⟨hul, huu, hvl, hvu, hdl, hdu⟩ := hex_coordinate_bounds hp
  by_cases hu : 0 ≤ coordU p
  · by_cases hv : 0 ≤ coordV p
    · by_cases huv : coordV p ≤ coordU p
      · refine ⟨0, ?_⟩
        rw [← reconstruct p]
        exact sector_zero _ _ hv huv huu
      · refine ⟨1, ?_⟩
        rw [← reconstruct p]
        exact sector_one _ _ hu (by linarith) hvu
    · refine ⟨5, ?_⟩
      rw [← reconstruct p]
      exact sector_five _ _ hu (by linarith) hdu
  · by_cases hv : 0 ≤ coordV p
    · refine ⟨2, ?_⟩
      rw [← reconstruct p]
      exact sector_two _ _ (by linarith) hv (by linarith)
    · by_cases huv : coordU p ≤ coordV p
      · refine ⟨3, ?_⟩
        rw [← reconstruct p]
        exact sector_three _ _ huv (by linarith) hul
      · refine ⟨4, ?_⟩
        rw [← reconstruct p]
        exact sector_four _ _ (by linarith) (by linarith) hvl

/-- Six fan triangles and one harmless duplicate, in the problem's seven-role type. -/
def sevenConfig : Fin 7 → UnitTriangle := ![fan 0, fan 1, fan 2, fan 3, fan 4, fan 5, fan 0]

theorem sevenConfig_first (k : Fin 6) : sevenConfig k.castSucc = fan k := by
  fin_cases k <;> rfl

theorem unit_hexagon_covered : Covers 1 sevenConfig := by
  intro p hp
  obtain ⟨k, hk⟩ := six_fans_cover hp
  apply Set.mem_iUnion.mpr
  refine ⟨k.castSucc, ?_⟩
  rw [sevenConfig_first]
  exact hk

theorem exists_unit_hexagon_cover : ∃ config : Fin 7 → UnitTriangle, Covers 1 config :=
  ⟨sevenConfig, unit_hexagon_covered⟩

end

end HexagonCover.StandardCover
