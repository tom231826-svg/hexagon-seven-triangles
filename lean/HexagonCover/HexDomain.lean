import HexagonCover.StandardCover
import HexagonCover.Anchors
import HexagonCover.DistanceLeaf

/-! A sound exact point-domain checker for the original H1 owner trees.
Closed boundary points are allowed. The actual hexagon remains a convex hull. -/
namespace HexagonCover.HexDomain
open StandardCover DistanceLeaf Quadratic3

theorem fan_subset_hexagon (k : Fin 6) : (fan k).region ⊆ Hexagon 1 := by
  apply convexHull_min
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · change point 0 0 ∈ Hexagon 1
      rw [point_zero]
      exact interior_subset (zero_mem_interior_hexagon (by norm_num : (0 : ℝ) < 1))
    · exact hexVertex_mem 1 k
    · exact hexVertex_mem 1 (k + 1)
  · exact convex_hexagon 1

theorem mem_of_coordinate_bounds (p : Plane)
    (hu : -1 ≤ coordU p ∧ coordU p ≤ 1)
    (hv : -1 ≤ coordV p ∧ coordV p ≤ 1)
    (hd : -1 ≤ coordU p - coordV p ∧ coordU p - coordV p ≤ 1) :
    p ∈ Hexagon 1 := by
  by_cases hupos : 0 ≤ coordU p
  · by_cases hvpos : 0 ≤ coordV p
    · by_cases huv : coordV p ≤ coordU p
      · apply fan_subset_hexagon 0
        rw [← reconstruct p]
        exact sector_zero _ _ hvpos huv hu.2
      · apply fan_subset_hexagon 1
        rw [← reconstruct p]
        exact sector_one _ _ hupos (by linarith) hv.2
    · apply fan_subset_hexagon 5
      rw [← reconstruct p]
      exact sector_five _ _ hupos (by linarith) hd.2
  · by_cases hvpos : 0 ≤ coordV p
    · apply fan_subset_hexagon 2
      rw [← reconstruct p]
      exact sector_two _ _ (by linarith) hvpos (by linarith [hd.1])
    · by_cases huv : coordU p ≤ coordV p
      · apply fan_subset_hexagon 3
        rw [← reconstruct p]
        exact sector_three _ _ huv (by linarith) hu.1
      · apply fan_subset_hexagon 4
        rw [← reconstruct p]
        exact sector_four _ _ (by linarith) (by linarith) hv.1

def nonnegative (x : Number) : Bool := positive x || decide (x = (0, 0))

theorem nonnegative_sound (x : Number) (accepted : nonnegative x = true) :
    0 ≤ real x := by
  rcases Bool.or_eq_true_iff.mp accepted with hp | hz
  · exact (positive_sound x hp).le
  · have he : x = (0, 0) := of_decide_eq_true hz
    simp [he, real]

def bounded (x : Number) : Bool :=
  nonnegative (add (ofRat 1) x) && nonnegative (sub (ofRat 1) x)

theorem bounded_sound (x : Number) (accepted : bounded x = true) :
    -1 ≤ real x ∧ real x ≤ 1 := by
  obtain ⟨hl, hu⟩ := Bool.and_eq_true_iff.mp accepted
  have hl' := nonnegative_sound _ hl
  have hu' := nonnegative_sound _ hu
  simp only [real_add, real_sub, real_ofRat, Rat.cast_one] at hl' hu'
  constructor <;> linarith

def thirdRoot : Number := (0, 1/3)
def exactU (p : ExactPoint) : Number := add p.x (mul thirdRoot p.y)
def exactV (p : ExactPoint) : Number := mul (ofRat 2) (mul thirdRoot p.y)

theorem thirdRoot_real : real thirdRoot = (Real.sqrt 3)⁻¹ := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  simp only [thirdRoot, real]
  norm_num
  field_simp [sqrt3_ne_zero]
  nlinarith

theorem exactU_real (p : ExactPoint) : real (exactU p) = coordU (toPlane p) := by
  simp [exactU, coordU, toPlane, thirdRoot_real, div_eq_mul_inv, mul_comm]

theorem exactV_real (p : ExactPoint) : real (exactV p) = coordV (toPlane p) := by
  simp [exactV, coordV, toPlane, thirdRoot_real, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

def check (p : ExactPoint) : Bool :=
  [exactU p, exactV p, sub (exactU p) (exactV p)].all bounded

theorem check_sound (p : ExactPoint) (accepted : check p = true) :
    toPlane p ∈ Hexagon 1 := by
  have ha := List.all_eq_true.mp accepted
  have hu := bounded_sound (exactU p) (ha _ (by simp))
  have hv := bounded_sound (exactV p) (ha _ (by simp))
  have hd := bounded_sound (sub (exactU p) (exactV p)) (ha _ (by simp))
  rw [exactU_real] at hu
  rw [exactV_real] at hv
  rw [real_sub, exactU_real, exactV_real] at hd
  exact mem_of_coordinate_bounds (toPlane p) hu hv hd

end HexagonCover.HexDomain
