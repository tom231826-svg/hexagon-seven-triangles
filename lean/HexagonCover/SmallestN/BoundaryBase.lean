import HexagonCover.SourceCoordinates
import HexagonCover.DistanceLeaf

namespace HexagonCover.SmallestN.BoundaryBase
open DistanceLeaf Quadratic3

def exactVertex : Fin 6 → ExactPoint :=
  ![fromXYZ (1/2) 0 (1/2), fromXYZ (-1/2) 0 (1/2), fromXYZ (-1) 0 0,
    fromXYZ (-1/2) 0 (-1/2), fromXYZ (1/2) 0 (-1/2), fromXYZ 1 0 0]

theorem vertex_real (i : Fin 6) : toPlane (exactVertex i) = SourceCoordinates.vertex i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [exactVertex, SourceCoordinates.vertex, hexVertex, toPlane, fromXYZ,
      real, ofRat, point] <;> ring

def interpolate (p q : ExactPoint) (t : ℚ) : ExactPoint :=
  ⟨add (mul (ofRat (1-t)) p.x) (mul (ofRat t) q.x),
   add (mul (ofRat (1-t)) p.y) (mul (ofRat t) q.y)⟩

theorem interpolate_real (p q : ExactPoint) (t : ℚ) :
    toPlane (interpolate p q t) =
      AffineMap.lineMap (toPlane p) (toPlane q) (t : ℝ) := by
  rw [AffineMap.lineMap_apply_module]
  ext j
  fin_cases j <;>
    simp [toPlane, interpolate, point, real_add, real_mul, real_ofRat] <;> ring

def check (p : ExactPoint) (edge : Fin 6) (t : ℚ) : Bool :=
  decide (0 ≤ t ∧ t ≤ 1 ∧ p = interpolate (exactVertex edge) (exactVertex (edge+1)) t)

theorem check_sound (p : ExactPoint) (edge : Fin 6) (t : ℚ)
    (accepted : check p edge t = true) :
    (t : ℝ) ∈ Set.Icc 0 1 ∧ toPlane p =
      AffineMap.lineMap (SourceCoordinates.vertex edge) (SourceCoordinates.vertex (edge+1)) (t : ℝ) := by
  obtain ⟨ht0, ht1, hp⟩ := of_decide_eq_true accepted
  refine ⟨⟨by exact_mod_cast ht0, by exact_mod_cast ht1⟩, ?_⟩
  rw [hp, interpolate_real, vertex_real, vertex_real]

end HexagonCover.SmallestN.BoundaryBase
