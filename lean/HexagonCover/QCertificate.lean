import HexagonCover.DomainData
import HexagonCover.PointSegmentLeaf
import HexagonCover.SubsetNI
import HexagonCover.SupportWitness
import HexagonCover.OwnerTree

/-! Shared semantics for source-bound Q leaves. The family fixes the point
table and NI roles. A row's anchor is determined by its owner. -/
namespace HexagonCover.QCertificate
open DistanceLeaf DistanceData

def pointCount : Family → Nat
  | .q25 | .q35 => 253
  | .q45 => 366

def table (family : Family) : Fin (pointCount family + 7) → ExactPoint :=
  match family with
  | .q25 => DomainData.tableQ25
  | .q35 => DomainData.tableQ35
  | .q45 => DomainData.tableQ45

def niRole (family : Family) (owner : Fin 7) : Prop :=
  owner = (5 : Fin 7) ∨ owner = match family with
  | .q25 => 2
  | .q35 => 3
  | .q45 => 4

def anchor (family : Family) (owner : Fin 7) : Fin (pointCount family + 7) :=
  ⟨pointCount family + owner.val, Nat.add_lt_add_left owner.isLt _⟩

structure Row (family : Family) where
  factId : Nat
  originalFlag : Bool
  owner : Fin 7
  points : List (Fin (pointCount family))

def Row.token {family : Family} (row : Row family) : Nat :=
  row.factId + if row.originalFlag then 2 ^ 40 else 0

def Row.ids {family : Family} (row : Row family) : List (Fin (pointCount family + 7)) :=
  anchor family row.owner :: row.points.map (Fin.castLE (Nat.le_add_right _ _))

def Row.obligations {family : Family} (row : Row family) : List ExactPoint :=
  row.ids.map (table family)

def NonIntruding (T : UnitTriangle) : Prop :=
  ∀ p ∈ T.region, (1 : ℝ) / 4 ≤ ‖p‖ ^ 2

inductive Checked {family : Family} (row : Row family) : Prop
  | diameter (positions : Nat × Nat)
      (accepted : checkWitness row.obligations positions = true)
  | pointSegment (witness : PointSegmentLeaf.Witness) (roleNI : niRole family row.owner)
      (accepted : PointSegmentLeaf.check row.obligations
        (Quadratic3.ofRat (1 / 4)) witness = true)
  | support (certificate : SupportWitness.CheckedCertificate)
      (member : SupportWitness.membershipCheck row.obligations certificate.certificate = true)
  | interval (certificate : SubsetNI.Certificate row.obligations)
      (roleNI : niRole family row.owner)
      (accepted : SubsetNI.check row.obligations (1 / 4) certificate = true)

theorem Checked.excluded {family : Family} {row : Row family} (checked : Checked row) (T : UnitTriangle)
    (contained : ∀ p ∈ row.obligations, toPlane p ∈ T.region)
    (ni : niRole family row.owner → NonIntruding T) : False := by
  cases checked with
  | diameter positions accepted =>
    exact checkWitness_sound accepted T contained
  | pointSegment witness roleNI accepted =>
    apply PointSegmentLeaf.cannot_be_nonintruding accepted T contained
    intro p hp
    simpa only [Quadratic3.real_ofRat, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
      using ni roleNI p hp
  | support certificate member =>
    exact certificate.excluded row.obligations member T contained
  | interval certificate roleNI accepted =>
    apply SubsetNI.nonintrusion_impossible accepted T contained
    intro p hp
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using ni roleNI p hp

theorem Checked.excluded_on_path {family : Family} {row : Row family} (checked : Checked row)
    (config : Fin 7 → UnitTriangle) (path : OwnerTree.Path (Fin (pointCount family + 7)))
    (satisfies : OwnerTree.Satisfies
      (fun owner i => toPlane (table family i) ∈ (config owner).region) path)
    (assigned : ∀ i ∈ row.ids, i ∈ path row.owner)
    (ni : niRole family row.owner → NonIntruding (config row.owner)) : False := by
  apply checked.excluded (config row.owner) _ ni
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact satisfies row.owner i (assigned i hi)

#print axioms Checked.excluded_on_path
end HexagonCover.QCertificate
