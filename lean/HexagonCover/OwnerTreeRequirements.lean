import HexagonCover.OwnerTreeSteps

/-! A subtree can be certified once for all incoming paths that contain its
required points. At a branch, the query may discharge a requirement only in
the child for that same owner. This permits bottom-up checking in chunks. -/
namespace HexagonCover.OwnerTree

abbrev Requirements (Point : Type u) := Owner → Set Point

def Contains (path : Path Point) (needed : Requirements Point) : Prop :=
  ∀ owner point, point ∈ needed owner → point ∈ path owner

def CheckedWith [DecidableEq Point] (inDomain : Point → Bool)
    (allowed : Point → Owner → Bool) (leafCheck : Owner → List Point → Certificate → Bool)
    (tree : Tree Point Certificate) (needed : Requirements Point) : Prop :=
  ∀ path, Contains path needed → check inDomain allowed leafCheck tree path = true

theorem leaf_checked_with [DecidableEq Point] (inDomain : Point → Bool)
    (allowed : Point → Owner → Bool) (leafCheck : Owner → List Point → Certificate → Bool)
    (owner : Owner) (obligations : List Point) (certificate : Certificate)
    (needed : Requirements Point)
    (included : ∀ point ∈ obligations, point ∈ needed owner)
    (accepted : leafCheck owner obligations certificate = true) :
    CheckedWith inDomain allowed leafCheck (.leaf owner obligations certificate) needed := by
  intro path contains
  apply Bool.and_eq_true_iff.mpr
  refine ⟨List.all_eq_true.mpr ?_, accepted⟩
  intro point hpoint
  exact decide_eq_true (contains owner point (included point hpoint))

theorem branch_checked_with [DecidableEq Point] (inDomain : Point → Bool)
    (allowed : Point → Owner → Bool) (leafCheck : Owner → List Point → Certificate → Bool)
    (query : Point) (children : Owner → Tree Point Certificate)
    (childNeeds : Owner → Requirements Point) (needed : Requirements Point)
    (domain : inDomain query = true)
    (childrenChecked : ∀ child, allowed query child = true →
      CheckedWith inDomain allowed leafCheck (children child) (childNeeds child))
    (transfer : ∀ child, allowed query child = true → ∀ owner point,
      point ∈ childNeeds child owner → (owner = child ∧ point = query) ∨ point ∈ needed owner) :
    CheckedWith inDomain allowed leafCheck (.branch query children) needed := by
  intro path contains
  apply branch_checked inDomain allowed leafCheck query children path domain
  intro child legal
  apply childrenChecked child legal
  intro owner point hneed
  rcases transfer child legal owner point hneed with ⟨rfl, rfl⟩ | inherited
  · simp [push]
  · have onPath := contains owner point inherited
    by_cases h : owner = child
    · subst owner
      simpa [push] using List.mem_cons_of_mem query onPath
    · simpa [push, h] using onPath

def maskNeeds (masks : Owner → Nat) : Requirements (Fin n) :=
  fun owner => {point | (masks owner).testBit point.val = true}

def availableMask (masks : Owner → Nat) (query : Fin n) (child owner : Owner) : Nat :=
  masks owner ||| if owner = child then 2 ^ query.val else 0

theorem mask_transfer (masks childMasks : Owner → Nat) (query : Fin n)
    (child owner : Owner) (point : Fin n)
    (bound : childMasks owner &&& availableMask masks query child owner = childMasks owner)
    (needed : point ∈ maskNeeds childMasks owner) :
    (owner = child ∧ point = query) ∨ point ∈ maskNeeds masks owner := by
  change (childMasks owner).testBit point.val = true at needed
  have h := congrArg (fun m : Nat => m.testBit point.val) bound
  simp only [Nat.testBit_and, needed, Bool.true_and] at h
  simp only [availableMask, Nat.testBit_or] at h
  rcases Bool.or_eq_true_iff.mp h with inherited | atQuery
  · exact Or.inr inherited
  · by_cases heq : owner = child
    · refine Or.inl ⟨heq, Fin.ext ?_⟩
      simpa [heq, Nat.testBit_two_pow, eq_comm] using atQuery
    · simp [heq] at atQuery

#print axioms branch_checked_with
#print axioms mask_transfer
end HexagonCover.OwnerTree
