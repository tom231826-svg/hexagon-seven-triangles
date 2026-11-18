import HexagonCover.QTreeCheck
import HexagonCover.PointSegmentData
import HexagonCover.SupportWitnessData.Common
import HexagonCover.QNIData.Binding

/-! Reuse the production witnesses as opaque proofs. The exact source key,
coordinate obligations, and (where relevant) radius must match the tree row. -/
namespace HexagonCover.QBoundWitness
open DistanceLeaf DistanceData QCertificate

structure Key where
  family : Family
  factId : Nat
  originalFlag : Bool
  owner : Fin 7
  ids : List Nat
  deriving DecidableEq

def key {family : Family} (row : Row family) : Key :=
  ⟨family, row.factId, row.originalFlag, row.owner, row.ids.map Fin.val⟩

def Resolved {family : Family} (row : Row family) : Prop :=
  ∀ T : UnitTriangle, (∀ p ∈ row.obligations, toPlane p ∈ T.region) →
    (niRole family row.owner → NonIntruding T) → False

theorem fromChecked {family : Family} {row : Row family} (h : Checked row) : Resolved row :=
  fun T contained ni => h.excluded T contained ni

theorem fromDiameter {family : Family} {row : Row family} (w : DistanceData.CheckedWitness)
    (_bound : key row = ⟨w.data.family, w.data.factId, w.data.originalFlag, w.data.role, w.data.pointIds⟩)
    (points : row.obligations = w.data.points) : Resolved row :=
  fun T contained _ => w.excluded T (points ▸ contained)

theorem fromSupport {family : Family} {row : Row family} (w : SupportWitnessData.CheckedWitness)
    (_bound : key row = ⟨w.data.family, w.data.factId, w.data.originalFlag, w.data.role, w.data.pointIds⟩)
    (points : row.obligations = w.data.points) : Resolved row :=
  fun T contained _ => w.excluded T (points ▸ contained)

theorem fromSegment {family : Family} {row : Row family} (w : PointSegmentData.CheckedWitness)
    (_bound : key row = ⟨w.data.family, w.data.factId, w.data.originalFlag, w.data.role, w.data.pointIds⟩)
    (points : row.obligations = w.data.points) (radius : w.data.radiusSquared = 1 / 4)
    (isNI : niRole family row.owner) : Resolved row := by
  intro T contained ni
  apply w.excluded T (points ▸ contained)
  intro p hp
  simpa only [radius, Quadratic3.real_ofRat, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using ni isNI p hp

theorem fromInterval {family : Family} {row : Row family} (w : QNIData.CheckedInput)
    (_bound : key row = ⟨w.data.family, w.data.factId, w.data.originalFlag, w.data.role, w.data.pointIds⟩)
    (_token : row.token = w.data.originalToken)
    (points : row.obligations = w.data.points) (radius : w.data.radiusSquared = 1 / 4)
    (isNI : niRole family row.owner) : Resolved row := by
  intro T contained ni
  apply w.excluded T (points ▸ contained)
  intro p hp
  simpa only [radius, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using ni isNI p hp

theorem check_sound {family : Family} (lookup : Nat → Option (Row family))
    (resolved : ∀ token row, lookup token = some row → Resolved row)
    (tree : QTreeCheck.Tree family) (accepted : QTreeCheck.check lookup tree = true)
    (config : Fin 7 → UnitTriangle) (covered : Covers 1 config)
    (anchors : ∀ owner, toPlane (table family (anchor family owner)) ∈ (config owner).region)
    (ni : ∀ owner, niRole family owner → NonIntruding (config owner)) : False := by
  refine OwnerTree.check_sound (fun _ => true) OwnerTree.allOwners (QTreeCheck.leafCheck lookup)
    (fun i => toPlane (table family i) ∈ Hexagon 1)
    (fun owner i => toPlane (table family i) ∈ (config owner).region)
    (fun i _ => QTreeCheck.table_mem_hexagon family i) ?_ ?_ tree
    (QTreeCheck.initialPath family) accepted ?_
  · apply OwnerTree.coverage_allOwners
    intro i hi
    exact Set.mem_iUnion.mp (covered hi)
  · intro owner ids token hcheck howns
    cases hrow : lookup token with
    | none => simp [QTreeCheck.leafCheck, hrow] at hcheck
    | some row =>
      have bound : row.token = token ∧ row.owner = owner ∧ row.ids = ids :=
        of_decide_eq_true (by simpa only [QTreeCheck.leafCheck, hrow] using hcheck)
      apply resolved token row hrow (config row.owner) _ (ni row.owner)
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [bound.2.1]
      exact howns i (bound.2.2 ▸ hi)
  · intro owner i hi
    have heq : i = anchor family owner := by simpa [QTreeCheck.initialPath] using hi
    simpa only [heq] using anchors owner

#print axioms check_sound
#print axioms fromDiameter
#print axioms fromSupport
#print axioms fromSegment
#print axioms fromInterval
end HexagonCover.QBoundWitness
