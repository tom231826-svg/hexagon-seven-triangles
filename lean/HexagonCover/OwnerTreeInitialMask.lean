import HexagonCover.OwnerTreeMaskSteps

/-! Compare the incoming owner paths by seven bitset inclusions, so the
kernel need not enumerate every domain point at every chunk root. -/
namespace HexagonCover.OwnerTree

def listMask : List (Fin n) → Nat
  | [] => 0
  | p :: ps => 2 ^ p.val ||| listMask ps

theorem testBit_listMask (xs : List (Fin n)) (p : Fin n) :
    (listMask xs).testBit p.val = true ↔ p ∈ xs := by
  induction xs with
  | nil => simp [listMask]
  | cons q qs ih =>
    simp only [listMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl (Fin.ext h.symm)
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr h

theorem contains_of_mask_inclusion (path : Path (Fin n)) (masks : Owner → Nat)
    (included : ∀ owner, masks owner &&& listMask (path owner) = masks owner) :
    Contains path (maskNeeds masks) := by
  intro owner point required
  have required' : (masks owner).testBit point.val = true := required
  apply (testBit_listMask _ _).1
  have h := congrArg (fun bits => Nat.testBit bits point.val) (included owner)
  simpa only [Nat.testBit_and, required', Bool.true_and] using h

#print axioms contains_of_mask_inclusion
end HexagonCover.OwnerTree
