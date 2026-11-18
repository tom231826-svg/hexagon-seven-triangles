import HexagonCover.SupportWitness

/-! Exact transport of all event obligations from two signs per unordered
point pair. The three normal roles are cyclic permutations; swapping the
ordered endpoints changes only the sign. The existing full event condition
and actual-triangle soundness theorem remain unchanged. -/
namespace HexagonCover.SupportWitnessSymmetry
open DistanceLeaf Quadratic3 SupportWitness

def permutation (role normal : Fin 3) : Fin 3 :=
  ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0]] role normal

def shift {n : ℕ} (role : Fin 3) (selected : Selection n) : Selection n :=
  fun normal => selected (permutation role normal)

private theorem point_ext {p q : ExactPoint} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  simp_all

theorem rotate_inverse (w : ExactPoint) (role normal : Fin 3) :
    ExactSupport.rotate (ExactSupport.rotate w (ExactSupport.inverseRole role)) normal =
      ExactSupport.rotate w (permutation role normal) := by
  fin_cases role <;> fin_cases normal <;> apply point_ext <;> apply Prod.ext <;>
    norm_num [ExactSupport.rotate, ExactSupport.inverseRole, ExactSupport.halfRoot,
      permutation, ofRat, add, sub, neg, mul] <;> ring

theorem rotate_eventBase (p q : ExactPoint) (role normal : Fin 3) (negative : Bool) :
    ExactSupport.rotate (ExactSupport.eventBase p q role negative) normal =
      ExactSupport.rotate
        (if negative then ExactSupport.negate (ExactSupport.perpendicular (ExactSupport.difference q p))
         else ExactSupport.perpendicular (ExactSupport.difference q p))
        (permutation role normal) := by
  exact rotate_inverse _ role normal

theorem eventSum_rotation {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool) (selected : Selection n) :
    eventSum points p q role negative (shift role selected) =
      eventSum points p q 0 negative selected := by
  unfold eventSum
  simp only [rotate_eventBase]
  fin_cases role <;> apply Prod.ext <;> simp [shift, permutation, add] <;> ring

theorem eventCheck_rotation {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool) (selected : Selection n) :
    eventCheck points p q role negative (shift role selected) =
      eventCheck points p q 0 negative selected := by
  unfold eventCheck
  rw [eventSum_rotation]

theorem squaredDistance_comm (p q : ExactPoint) : squaredDistance p q = squaredDistance q p := by
  apply Prod.ext <;> simp [squaredDistance, add, square, sub, neg, mul] <;> ring

theorem eventBase_swap (p q : ExactPoint) (role : Fin 3) (negative : Bool) :
    ExactSupport.eventBase p q role negative = ExactSupport.eventBase q p role (!negative) := by
  unfold ExactSupport.eventBase
  apply congrArg (fun w => ExactSupport.rotate w (ExactSupport.inverseRole role))
  cases negative <;> apply point_ext <;> apply Prod.ext <;>
    simp [ExactSupport.negate, ExactSupport.perpendicular, ExactSupport.difference, neg, sub, add] <;> ring

theorem eventCheck_swap {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (p q : ExactPoint) (role : Fin 3) (negative : Bool) (selected : Selection n) :
    eventCheck points p q role negative selected =
      eventCheck points q p role (!negative) selected := by
  have hs : eventSum points p q role negative selected =
      eventSum points q p role (!negative) selected := by
    unfold eventSum
    rw [eventBase_swap p q role negative]
  unfold eventCheck
  rw [hs, squaredDistance_comm p q]

abbrev ReducedSelections (n : ℕ) := Fin (n+1) → Fin (n+1) → Bool → Selection n

def extend {n : ℕ} (selected : ReducedSelections n) : Selections n :=
  fun i j role negative => if i < j then shift role (selected i j negative)
    else shift role (selected j i (!negative))

structure ReducedChecked {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : ReducedSelections n) : Prop where
  distinct : ∃ i j, positive (squaredDistance (points i) (points j)) = true
  events : ∀ i j, i < j → ∀ negative,
    eventCheck points (points i) (points j) 0 negative (selected i j negative) = true

theorem extend_checked {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : ReducedSelections n) (accepted : ReducedChecked points selected) :
    Checked points (extend selected) := by
  refine ⟨accepted.distinct, ?_⟩
  intro i j hij role negative
  by_cases hlt : i < j
  · simp only [extend, hlt, ↓reduceIte]
    rw [eventCheck_rotation]
    exact accepted.events i j hlt negative
  · have hne : i ≠ j := fun h => hij (congrArg points h)
    have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    simp only [extend, hlt, ↓reduceIte]
    rw [eventCheck_rotation, eventCheck_swap]
    exact accepted.events j i hji (!negative)

theorem checked_sound {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (selected : ReducedSelections n) (accepted : ReducedChecked points selected)
    (T : UnitTriangle) (contained : ∀ j, toPlane (points j) ∈ T.region) : False :=
  SupportWitness.checked_sound points (extend selected) (extend_checked points selected accepted) T contained

end HexagonCover.SupportWitnessSymmetry
