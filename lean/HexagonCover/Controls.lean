import HexagonCover.Diametric
import HexagonCover.DistanceLeaf
import HexagonCover.OwnerTree

/-! Explicit feasible geometry and malformed-leaf controls. These are local
controls, not yet the six-piece standard-fan covering theorem. -/
namespace HexagonCover.Controls

noncomputable section

def standardVertices : Fin 3 → Plane :=
  ![point 0 0, point 1 0, point (1/2) pilotH]

theorem standard_edge (i j : Fin 3) (hij : i ≠ j) :
    dist (standardVertices i) (standardVertices j) = 1 := by
  have hsq : dist (standardVertices i) (standardVertices j) ^ 2 = 1 := by
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals
      change dist (point _ _) (point _ _) ^ 2 = 1
      rw [dist_point_sq]
      nlinarith [pilotH_sq]
  have hn : 0 ≤ dist (standardVertices i) (standardVertices j) := dist_nonneg
  nlinarith

def standardTriangle : UnitTriangle := ⟨standardVertices, standard_edge⟩

def tangentVertices : Fin 3 → Plane :=
  ![point (-(1/2 : ℝ)) (1/2), point (1/2) (1/2), point 0 (1/2+pilotH)]

theorem tangent_edge (i j : Fin 3) (hij : i ≠ j) :
    dist (tangentVertices i) (tangentVertices j) = 1 := by
  have hsq : dist (tangentVertices i) (tangentVertices j) ^ 2 = 1 := by
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals norm_num [tangentVertices, dist_point_sq] <;> nlinarith [pilotH_sq]
  have hn : 0 ≤ dist (tangentVertices i) (tangentVertices j) := dist_nonneg
  nlinarith

def tangentTriangle : UnitTriangle := ⟨tangentVertices, tangent_edge⟩

theorem tangent_nonintrusion : ∀ z ∈ tangentTriangle.region, (1/2 : ℝ) ≤ ‖z‖ := by
  have hsub : tangentTriangle.region ⊆ {z : Plane | (1/2 : ℝ) ≤ z 1} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [tangentTriangle, tangentVertices] <;> linarith [pilotH_pos]
    · intro x hx y hy a b ha hb hab
      change (1/2 : ℝ) ≤ a * x 1 + b * y 1
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hy)]
  intro z hz
  have hy := hsub hz
  change (1/2 : ℝ) ≤ z 1 at hy
  have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    simpa only [point_eta] using norm_point_sq (z 0) (z 1)
  have hn := norm_nonneg z
  nlinarith [sq_nonneg (z 0)]

theorem tangent_contact : point 0 (1/2) ∈ tangentTriangle.region := by
  have h := tangentTriangle.convex_region (tangentTriangle.vertex_mem 0)
    (tangentTriangle.vertex_mem 1) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+(1/2)=1)
  have heq : (1/2 : ℝ) • tangentTriangle.vertex 0 + (1/2 : ℝ) • tangentTriangle.vertex 1 =
      point 0 (1/2) := by
    ext i
    fin_cases i <;> norm_num [tangentTriangle,tangentVertices,point]
  rwa [heq] at h

end

open DistanceLeaf in
theorem unit_distance_is_not_rejected : check (fromXYZ 0 0 0) (fromXYZ 1 0 0) = false := by
  decide +kernel

open DistanceLeaf in
theorem invalid_distance_index_is_rejected :
    checkWitness [fromXYZ 1 0 0, fromXYZ (-1) 0 0] (0, 2) = false := by
  decide +kernel

open DistanceLeaf OwnerTree in
def missingPathTree : Tree ExactPoint (Nat × Nat) :=
  .leaf 0 [fromXYZ 1 0 0, fromXYZ (-1) 0 0] (0,1)

open DistanceLeaf OwnerTree in
theorem missing_path_is_rejected :
    OwnerTree.check (fun _ => true) (fun _ _ => true)
      (fun _ points witness => checkWitness points witness)
      missingPathTree emptyPath = false := by
  decide +kernel

end HexagonCover.Controls
