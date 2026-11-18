import Mathlib

/-!+# Finite trees of point owners

This module proves the purely logical part of a covering certificate. A branch
has exactly seven indexed children. Its queried point must pass the domain
checker, and every legal owner child must pass. A leaf cites a single owner and
points already assigned to that same owner. Its geometric certificate is checked
by a parameter supplied by the caller.

The theorem is conditional on the soundness of that parameter and the domain
checker. It is not a geometric theorem about triangles. The allowed-owner
predicate may give six owners at one point and seven at another, provided that
the coverage hypothesis supplies at least one legal owner for each queried
point. No covering owner is assumed unique.

The tree argument is derived by induction. No historical parser, stored success
flag, or certificate count is a premise of its soundness theorem.
-/

namespace HexagonCover.OwnerTree

abbrev Owner := Fin 7

/-- A genuinely finite tree; function-valued children still have exactly seven
indices. There is no constructor for a missing or unresolved legal branch. -/
inductive Tree (Point : Type u) (Certificate : Type v) where
  | leaf (owner : Owner) (obligations : List Point) (certificate : Certificate)
  | branch (point : Point) (children : Owner → Tree Point Certificate)

/-- Each owner has its own accumulated obligations, including any initial
mandatory points whose ownership is supplied by the application. -/
abbrev Path (Point : Type u) := Owner → List Point

def emptyPath : Path Point := fun _ => []

/-- Assign the new point to only the selected owner. Other owners' paths are
preserved. Multiple ownership in the actual configuration causes no difficulty. -/
def push (path : Path Point) (owner : Owner) (point : Point) : Path Point :=
  fun other => if other = owner then point :: path other else path other

/-- A particular hypothetical configuration satisfies the accumulated paths. -/
def Satisfies (Owns : Owner → Point → Prop) (path : Path Point) : Prop :=
  ∀ owner point, point ∈ path owner → Owns owner point

theorem satisfies_empty (Owns : Owner → Point → Prop) :
    Satisfies Owns emptyPath := by
  intro owner point h
  simp [emptyPath] at h

theorem satisfies_push {Owns : Owner → Point → Prop} {path : Path Point}
    {owner : Owner} {point : Point}
    (hpath : Satisfies Owns path) (hpoint : Owns owner point) :
    Satisfies Owns (push path owner point) := by
  intro other q hq
  by_cases h : other = owner
  · have hmem : q ∈ point :: path owner := by
      simpa [push, h] using hq
    have howned : Owns owner q := by
      rcases List.mem_cons.mp hmem with heq | hprevious
      · simpa only [heq] using hpoint
      · exact hpath owner q hprevious
    simpa only [h] using howned
  · have hmem : q ∈ path other := by
      simpa [push, h] using hq
    exact hpath other q hmem

/-- The executable checker. Geometry and packet necessity are external
parameters; they become explicit hypotheses in `check_sound`.

`decide` here computes only finite owner enumeration and decidable equalities.
It does not accept an asserted proposition as a certificate. -/
def check [DecidableEq Point]
    (inDomain : Point → Bool)
    (allowed : Point → Owner → Bool)
    (leafCheck : Owner → List Point → Certificate → Bool) :
    Tree Point Certificate → Path Point → Bool
  | .leaf owner obligations certificate, path =>
      obligations.all (fun point => decide (point ∈ path owner)) &&
        leafCheck owner obligations certificate
  | .branch point children, path =>
      inDomain point &&
        decide (∀ owner : Owner, allowed point owner = true →
          check inDomain allowed leafCheck (children owner) (push path owner point) = true)

/-- Logical tree soundness for one hypothetical actual configuration.

* `domainSound` connects the executable point-domain test to its mathematical
  domain.
* `coverage` must supply a legal covering owner, and permits overlapping owners.
* `leafSound` must rule out a triangle/configuration containing the stated
  same-owner points whenever the actual leaf checker returns true.

Nothing in this theorem asserts those geometric premises. -/
theorem check_sound [DecidableEq Point]
    (inDomain : Point → Bool)
    (allowed : Point → Owner → Bool)
    (leafCheck : Owner → List Point → Certificate → Bool)
    (Domain : Point → Prop)
    (Owns : Owner → Point → Prop)
    (domainSound : ∀ point, inDomain point = true → Domain point)
    (coverage : ∀ point, Domain point →
      ∃ owner, allowed point owner = true ∧ Owns owner point)
    (leafSound : ∀ owner obligations certificate,
      leafCheck owner obligations certificate = true →
      (∀ point, point ∈ obligations → Owns owner point) → False)
    (tree : Tree Point Certificate) (path : Path Point)
    (accepted : check inDomain allowed leafCheck tree path = true)
    (pathSatisfied : Satisfies Owns path) : False := by
  induction tree generalizing path with
  | leaf owner obligations certificate =>
      obtain ⟨allOnPath, leafAccepted⟩ := Bool.and_eq_true_iff.mp accepted
      apply leafSound owner obligations certificate leafAccepted
      intro point hpoint
      apply pathSatisfied owner point
      exact of_decide_eq_true ((List.all_eq_true.mp allOnPath) point hpoint)
  | branch point children inductionHypothesis =>
      obtain ⟨domainAccepted, childrenAccepted⟩ := Bool.and_eq_true_iff.mp accepted
      have eachChild : ∀ owner : Owner, allowed point owner = true →
          check inDomain allowed leafCheck (children owner) (push path owner point) = true :=
        of_decide_eq_true childrenAccepted
      obtain ⟨owner, ownerAllowed, ownerCovers⟩ :=
        coverage point (domainSound point domainAccepted)
      exact inductionHypothesis owner (push path owner point)
        (eachChild owner ownerAllowed) (satisfies_push pathSatisfied ownerCovers)

/-- At an empty initial path the only remaining hypotheses are actual coverage,
domain-checker soundness and geometric-leaf-checker soundness. -/
theorem check_empty_sound [DecidableEq Point]
    (inDomain : Point → Bool)
    (allowed : Point → Owner → Bool)
    (leafCheck : Owner → List Point → Certificate → Bool)
    (Domain : Point → Prop)
    (Owns : Owner → Point → Prop)
    (domainSound : ∀ point, inDomain point = true → Domain point)
    (coverage : ∀ point, Domain point →
      ∃ owner, allowed point owner = true ∧ Owns owner point)
    (leafSound : ∀ owner obligations certificate,
      leafCheck owner obligations certificate = true →
      (∀ point, point ∈ obligations → Owns owner point) → False)
    (tree : Tree Point Certificate)
    (accepted : check inDomain allowed leafCheck tree emptyPath = true) : False :=
  check_sound inDomain allowed leafCheck Domain Owns domainSound coverage leafSound
    tree emptyPath accepted (satisfies_empty Owns)

/-- The usual unrestricted seven-owner case. -/
def allOwners (_ : Point) (_ : Owner) : Bool := true

/-- Ordinary coverage supplies the legal-owner hypothesis for `allOwners`.
The existential permits any number of overlapping covering owners. -/
theorem coverage_allOwners {Domain : Point → Prop} {Owns : Owner → Point → Prop}
    (coverage : ∀ point, Domain point → ∃ owner, Owns owner point) :
    ∀ point, Domain point →
      ∃ owner, allOwners point owner = true ∧ Owns owner point := by
  intro point hpoint
  obtain ⟨owner, howner⟩ := coverage point hpoint
  exact ⟨owner, rfl, howner⟩

end HexagonCover.OwnerTree
