import HexagonCover.OwnerTreeInitialMask

/-! A large original tree can be certified in closed blocks. A tip is
permitted only with an already-proved subtree and its requirement mask.
Every other child of an allowed branch is checked here. -/
namespace HexagonCover.OwnerTree

def allSeven (f : Owner → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6

theorem allSeven_true {f : Owner → Bool} (h : allSeven f = true) (i : Owner) : f i = true := by
  simp only [allSeven, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨h0,h1⟩,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

inductive Chunk (inDomain : Fin n → Bool) (allowed : Fin n → Owner → Bool)
    (leafCheck : Owner → List (Fin n) → Certificate → Bool) where
  | leaf (owner : Owner) (ids : List (Fin n)) (certificate : Certificate)
  | branch (query : Fin n) (mask : Owner → Nat) (children : Owner → Chunk inDomain allowed leafCheck)
  | tip (tree : Tree (Fin n) Certificate) (mask : Owner → Nat)
      (proved : CheckedWith inDomain allowed leafCheck tree (maskNeeds mask))

variable {n : Nat} {Certificate : Type u} {inDomain : Fin n → Bool}
  {allowed : Fin n → Owner → Bool} {leafCheck : Owner → List (Fin n) → Certificate → Bool}

def Chunk.tree : Chunk inDomain allowed leafCheck → Tree (Fin n) Certificate
  | .leaf owner ids certificate => .leaf owner ids certificate
  | .branch query _ children => .branch query (fun owner => (children owner).tree)
  | .tip tree _ _ => tree

def Chunk.mask : Chunk inDomain allowed leafCheck → Owner → Nat
  | .leaf owner ids _ => fun i => if i = owner then listMask ids else 0
  | .branch _ mask _ => mask
  | .tip _ mask _ => mask

def Chunk.accepted : Chunk inDomain allowed leafCheck → Bool
  | .leaf owner ids certificate => leafCheck owner ids certificate
  | .branch query mask children => inDomain query && allSeven (fun child =>
      if allowed query child then
        (children child).accepted && allSeven (fun owner =>
          decide ((children child).mask owner &&& availableMask mask query child owner =
            (children child).mask owner))
      else true)
  | .tip .. => true

theorem Chunk.sound (c : Chunk inDomain allowed leafCheck) (h : c.accepted = true) :
    CheckedWith inDomain allowed leafCheck c.tree (maskNeeds c.mask) := by
  induction c with
  | leaf owner ids certificate =>
    apply leaf_checked_with inDomain allowed leafCheck owner ids certificate
    · intro p hp
      change (if owner = owner then listMask ids else 0).testBit p.val = true
      rw [ite_eq_left rfl]
      exact (testBit_listMask ids p).2 hp
    · exact h
  | branch query mask children ih =>
    have pair := Bool.and_eq_true_iff.mp h
    apply branch_checked_masks inDomain allowed leafCheck query
      (fun owner => (children owner).tree) (fun child => (children child).mask) mask pair.1
    · intro child legal
      apply ih child
      have raw := allSeven_true pair.2 child
      rw [ite_eq_left legal] at raw
      exact (Bool.and_eq_true_iff.mp raw).1
    · intro child legal owner
      have raw := allSeven_true pair.2 child
      rw [ite_eq_left legal] at raw
      exact of_decide_eq_true (allSeven_true (Bool.and_eq_true_iff.mp raw).2 owner)
  | tip tree mask proved =>
    exact proved

#print axioms Chunk.sound
end HexagonCover.OwnerTree
