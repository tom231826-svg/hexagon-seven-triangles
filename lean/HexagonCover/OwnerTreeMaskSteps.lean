import HexagonCover.OwnerTreeRequirements

/-! Local certificates for trees whose point IDs have a finite bound. Numerical
work is limited to the leaves and transfers of one node at a time. -/
namespace HexagonCover.OwnerTree

theorem leaf_checked_masks (inDomain : Fin n → Bool)
    (allowed : Fin n → Owner → Bool) (leafCheck : Owner → List (Fin n) → Certificate → Bool)
    (owner : Owner) (obligations : List (Fin n)) (certificate : Certificate)
    (masks : Owner → Nat)
    (included : obligations.all (fun p => (masks owner).testBit p.val) = true)
    (accepted : leafCheck owner obligations certificate = true) :
    CheckedWith inDomain allowed leafCheck (.leaf owner obligations certificate) (maskNeeds masks) :=
  leaf_checked_with inDomain allowed leafCheck owner obligations certificate (maskNeeds masks)
    (List.all_eq_true.mp included) accepted

theorem branch_checked_masks (inDomain : Fin n → Bool)
    (allowed : Fin n → Owner → Bool) (leafCheck : Owner → List (Fin n) → Certificate → Bool)
    (query : Fin n) (children : Owner → Tree (Fin n) Certificate)
    (childMasks : Owner → Owner → Nat) (masks : Owner → Nat)
    (domain : inDomain query = true)
    (childrenChecked : ∀ child, allowed query child = true →
      CheckedWith inDomain allowed leafCheck (children child) (maskNeeds (childMasks child)))
    (transfers : ∀ child, allowed query child = true → ∀ owner,
      childMasks child owner &&& availableMask masks query child owner = childMasks child owner) :
    CheckedWith inDomain allowed leafCheck (.branch query children) (maskNeeds masks) := by
  apply branch_checked_with inDomain allowed leafCheck query children
    (fun child => maskNeeds (childMasks child)) (maskNeeds masks) domain childrenChecked
  intro child legal owner point need
  exact mask_transfer masks (childMasks child) query child owner point (transfers child legal owner) need

#print axioms branch_checked_masks
end HexagonCover.OwnerTree
