import HexagonCover.ContinuousSupport

/-! Exact real-coordinate event permutation: two signs per unordered pair
imply every normal role and both ordered point directions. -/
namespace HexagonCover.ContinuousSupportSymmetry
open TriangleFrame SupportGeometry ContinuousSupport
noncomputable section

def permutation (role normal : Fin 3) : Fin 3 :=
  ![![0,1,2],![2,0,1],![1,2,0]] role normal
def shift {n : ℕ} (role : Fin 3) (selected : Fin 3 → Fin (n+1)) : Fin 3 → Fin (n+1) :=
  fun normal=>selected (permutation role normal)

theorem selected_rotation {n : ℕ} (points : Fin (n+1) → Plane) (j k : Fin (n+1))
    (role : Fin 3) (negative : Bool) (selected : Fin 3 → Fin (n+1)) :
    selectedSum points j k role negative (shift role selected)=
      selectedSum points j k 0 negative selected := by
  unfold selectedSum branch
  rw [Fin.sum_univ_three,Fin.sum_univ_three]
  fin_cases role <;> cases negative
  all_goals
    simp [eventBase,signedPerpendicular,perpendicular,inverseRole,nvec,
      NICertificate.normalValues,shift,permutation,dotp,point] <;>
      ring_nf <;> simp only [ExtremeTriangle.halfRoot_sq] <;> ring

theorem selected_swap {n : ℕ} (points : Fin (n+1) → Plane) (j k : Fin (n+1))
    (role : Fin 3) (negative : Bool) (selected : Fin 3 → Fin (n+1)) :
    selectedSum points j k role negative selected=selectedSum points k j role (!negative) selected := by
  unfold selectedSum
  rw [eventBase_swap]

def extend {n : ℕ} (selected : Fin (n+1) → Fin (n+1) → Bool → Fin 3 → Fin (n+1)) :
    Fin (n+1) → Fin (n+1) → Fin 3 → Bool → Fin 3 → Fin (n+1) :=
  fun j k role negative=>if j < k then shift role (selected j k negative)
    else shift role (selected k j (!negative))

theorem impossible {n : ℕ} (points : Fin (n+1) → Plane)
    {a b : Fin (n+1)} (distinct : points a≠points b)
    (selected : Fin (n+1) → Fin (n+1) → Bool → Fin 3 → Fin (n+1))
    (checked : ∀j k, j < k → ∀negative,
      0 < selectedSum points j k 0 negative (selected j k negative) ∧
      NICertificate.halfRoot^2*‖points k-points j‖^2 <
        (selectedSum points j k 0 negative (selected j k negative))^2)
    (T : UnitTriangle) (contained : ∀j,points j∈T.region) : False := by
  apply ContinuousSupport.impossible points distinct (extend selected) ?_ T contained
  intro j k hjk role negative
  by_cases hlt : j < k
  · simp only [extend,hlt,↓reduceIte,selected_rotation]
    exact checked j k hlt negative
  · have hrev : k < j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hjk)
    simp only [extend,hlt,↓reduceIte,selected_rotation]
    have hs := selected_swap points j k 0 negative (selected k j (!negative))
    simp only [hs]
    simpa only [norm_sub_rev] using checked k j hrev (!negative)

end
end HexagonCover.ContinuousSupportSymmetry
