import HexagonCover.QCertificate

/-! Connect source tokens to actual owner paths. Every branch retains all seven
owners, including nodes with an original `forced` annotation. -/
namespace HexagonCover.QTreeCheck
open DistanceLeaf DistanceData QCertificate

abbrev Point (family : Family) := Fin (pointCount family + 7)
abbrev Tree (family : Family) := OwnerTree.Tree (Point family) Nat

def initialPath (family : Family) : OwnerTree.Path (Point family) :=
  fun owner => [anchor family owner]

def leafCheck (lookup : Nat → Option (Row family))
    (owner : Fin 7) (ids : List (Point family)) (token : Nat) : Bool :=
  match lookup token with
  | none => false
  | some row => decide (row.token = token ∧ row.owner = owner ∧ row.ids = ids)

def check (lookup : Nat → Option (Row family)) (tree : Tree family) : Bool :=
  OwnerTree.check (fun _ => true) OwnerTree.allOwners (leafCheck lookup)
    tree (initialPath family)

theorem table_mem_hexagon (family : Family) (i : Point family) :
    toPlane (table family i) ∈ Hexagon 1 := by
  cases family
  · exact DomainData.domainQ25 i
  · exact DomainData.domainQ35 i
  · exact DomainData.domainQ45 i

theorem check_sound {family : Family} (lookup : Nat → Option (Row family))
    (resolved : ∀ token row, lookup token = some row → Checked row)
    (tree : Tree family) (accepted : check lookup tree = true)
    (config : Fin 7 → UnitTriangle) (covered : Covers 1 config)
    (anchors : ∀ owner, toPlane (table family (anchor family owner)) ∈ (config owner).region)
    (ni : ∀ owner, niRole family owner → NonIntruding (config owner)) : False := by
  refine OwnerTree.check_sound (fun _ => true) OwnerTree.allOwners (leafCheck lookup)
    (fun i => toPlane (table family i) ∈ Hexagon 1)
    (fun owner i => toPlane (table family i) ∈ (config owner).region)
    (fun i _ => table_mem_hexagon family i) ?_ ?_ tree (initialPath family) accepted ?_
  · apply OwnerTree.coverage_allOwners
    intro i hi
    exact Set.mem_iUnion.mp (covered hi)
  · intro owner ids token hcheck howns
    cases hrow : lookup token with
    | none => simp [leafCheck, hrow] at hcheck
    | some row =>
      have bound : row.token = token ∧ row.owner = owner ∧ row.ids = ids :=
        of_decide_eq_true (by simpa only [leafCheck, hrow] using hcheck)
      apply (resolved token row hrow).excluded (config row.owner) _ (ni row.owner)
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [bound.2.1]
      exact howns i (bound.2.2 ▸ hi)
  · intro owner i hi
    have heq : i = anchor family owner := by simpa [initialPath] using hi
    simpa only [heq] using anchors owner

#print axioms check_sound
end HexagonCover.QTreeCheck
