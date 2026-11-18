import Mathlib

/-!
# The exact planar covering problem

The definitions below keep the triangles as actual translated and rotated closed
unit equilateral triangles.  `CoverConjecture` records the requested statement; it
is a definition of a proposition, not a claim that the proposition has been proved.
-/

namespace HexagonCover

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Cartesian coordinates in the Euclidean plane. -/
def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

@[simp] theorem point_zero : point 0 0 = 0 := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem point_coord_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] theorem point_coord_one (x y : ℝ) : point x y 1 = y := rfl

theorem norm_point_sq (x y : ℝ) : ‖point x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

theorem dist_point_sq (x y x' y' : ℝ) :
    dist (point x y) (point x' y') ^ 2 = (x - x') ^ 2 + (y - y') ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [point, Fin.sum_univ_two]

/-- An actual closed equilateral triangle of side length one. -/
structure UnitTriangle where
  vertex : Fin 3 → Plane
  edgeLength : ∀ i j, i ≠ j → dist (vertex i) (vertex j) = 1

namespace UnitTriangle

/-- The full closed triangular region, including its boundary. -/
def region (T : UnitTriangle) : Set Plane := convexHull ℝ (Set.range T.vertex)

theorem vertex_mem (T : UnitTriangle) (i : Fin 3) : T.vertex i ∈ T.region :=
  subset_convexHull ℝ (Set.range T.vertex) ⟨i, rfl⟩

theorem convex_region (T : UnitTriangle) : Convex ℝ T.region :=
  convex_convexHull ℝ (Set.range T.vertex)

theorem compact_region (T : UnitTriangle) : IsCompact T.region :=
  (Set.finite_range T.vertex).isCompact_convexHull ℝ

theorem closed_region (T : UnitTriangle) : IsClosed T.region :=
  T.compact_region.isClosed

/-- Every pair of points of the entire triangle is at distance at most one. -/
theorem dist_le_one (T : UnitTriangle) {x y : Plane}
    (hx : x ∈ T.region) (hy : y ∈ T.region) : dist x y ≤ 1 := by
  have hvv : ∀ i j, dist (T.vertex i) (T.vertex j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst j
      simp
    · exact le_of_eq (T.edgeLength i j h)
  have hball : ∀ i, T.region ⊆ Metric.closedBall (T.vertex i) 1 := by
    intro i
    apply convexHull_min
    · rintro _ ⟨j, rfl⟩
      exact hvv j i
    · exact convex_closedBall (T.vertex i) 1
  have hsub : T.region ⊆ Metric.closedBall y 1 := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      have h := hball i hy
      simpa only [Metric.mem_closedBall, dist_comm] using h
    · exact convex_closedBall y 1
  exact hsub hx

end UnitTriangle

/-- The six vertices of the regular hexagon, in counterclockwise order. -/
def hexVertex (s : ℝ) : Fin 6 → Plane :=
  ![point s 0,
    point (s / 2) (Real.sqrt 3 * s / 2),
    point (-s / 2) (Real.sqrt 3 * s / 2),
    point (-s) 0,
    point (-s / 2) (-Real.sqrt 3 * s / 2),
    point (s / 2) (-Real.sqrt 3 * s / 2)]

/-- The closed regular hexagon centered at the origin with side length `s`. -/
def Hexagon (s : ℝ) : Set Plane := convexHull ℝ (Set.range (hexVertex s))

theorem convex_hexagon (s : ℝ) : Convex ℝ (Hexagon s) :=
  convex_convexHull ℝ (Set.range (hexVertex s))

theorem compact_hexagon (s : ℝ) : IsCompact (Hexagon s) :=
  (Set.finite_range (hexVertex s)).isCompact_convexHull ℝ

theorem hexVertex_mem (s : ℝ) (i : Fin 6) : hexVertex s i ∈ Hexagon s :=
  subset_convexHull ℝ (Set.range (hexVertex s)) ⟨i, rfl⟩

/-- Seven actual triangles cover every point of the closed hexagon. -/
def Covers (s : ℝ) (config : Fin 7 → UnitTriangle) : Prop :=
  Hexagon s ⊆ ⋃ i, (config i).region

/-- The exact target conjecture. This definition is not a proof of it. -/
def CoverConjecture : Prop :=
  ∀ s : ℝ, 1 < s → ∀ config : Fin 7 → UnitTriangle, ¬ Covers s config

end

end HexagonCover
