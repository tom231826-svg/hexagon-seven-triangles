import HexagonCover.NISubsetData.Batch0000

/-! Concrete negative controls for the original N8100_8300 fact 402, role 5.
Its 82-cell certificate is already used by SmallestN.  We remove its first
orientation cell, or replace just the first witness of its first three-extreme
cell by an invalid raw edge.  `Fin 3 → IntrusionWitness` cannot omit a slot;
the latter is an explicit malformed-placeholder mutation, not a shorter tuple.
Neither test changes the original data, selected points, or squared radius.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace HexagonCover.FinalNIControls

open NISubsetData.Data0000 NISubsetData.Batch0000

abbrev points := c0000_points
abbrev radiusSquared := c0000_radius
abbrev original := NISubsetData.Batch0000.c0000_certificate
abbrev originalFirst := NISubsetData.Batch0000.c0000_cell0000

theorem original_accepted : SubsetNI.check points radiusSquared original = true :=
  c0000_checked

theorem original_payload_identical :
    original.forget = NISubsetData.Data0000.c0000_certificate :=
  c0000_payload_identical

theorem original_identity :
    c0000_band = "M8100_8300" ∧ c0000_factId = 402 ∧ c0000_role = 5 ∧
    c0000_pointIds = [5, 17, 18, 125, 169] ∧
    radiusSquared = 19683 / 40000 ∧ original.cells.length = 82 := by
  decide +kernel

def missingDirection : SubsetNI.Certificate points :=
  { original with cells := original.cells.tail }

theorem missing_direction_partition_rejected :
    NICertificate.partitionFrom (-1) 1
      (missingDirection.cells.map (fun cell => cell.original.1)) = false := by
  decide +kernel

theorem missing_direction_rejected :
    SubsetNI.check points radiusSquared missingDirection = false := by
  simp only [SubsetNI.check, missing_direction_partition_rejected,
    Bool.and_false, Bool.false_and]

def firstWitnesses : Fin 3 → GenericNI.IntrusionWitness :=
  match originalFirst.original.2 with
  | .threeExtremes witnesses => witnesses
  | .support => fun _ => .origin

theorem original_first_is_three_extremes :
    originalFirst.original.2 = .threeExtremes firstWitnesses := rfl

def malformedWitnesses : Fin 3 → GenericNI.IntrusionWitness :=
  fun i => if i = 0 then .segment ⟨3, 0, 0⟩ else firstWitnesses i

def malformedCell : SubsetNI.Cell points where
  original := (originalFirst.original.1, .threeExtremes malformedWitnesses)
  picks := originalFirst.picks

def malformedExtreme : SubsetNI.Certificate points :=
  { original with cells := malformedCell :: original.cells.tail }

theorem other_extremes_preserved :
    malformedWitnesses 1 = firstWitnesses 1 ∧
    malformedWitnesses 2 = firstWitnesses 2 := by
  constructor <;> rfl

theorem malformed_payload_preserves_other_fields :
    malformedCell.original.1 = originalFirst.original.1 ∧
    malformedCell.selected = originalFirst.selected ∧
    malformedExtreme.cells.tail = original.cells.tail ∧
    malformedExtreme.frontier = original.frontier := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- All three slots are present in the type; a malformed first slot is rejected
for every possible remaining pair, before any interval arithmetic is needed. -/
theorem invalid_first_extreme_rejected (ps : List DistanceLeaf.ExactPoint)
    (r : ℚ) (C S : Exact.Interval) (w : Fin 3 → GenericNI.IntrusionWitness) :
    GenericNI.leafCheck ps r C S
      (.threeExtremes (fun i => if i = 0 then .segment ⟨3, 0, 0⟩ else w i)) = false := by
  simp [GenericNI.leafCheck, GenericNI.extremeCheck]

theorem malformed_cell_rejected :
    GenericNI.cellCheck malformedCell.selected radiusSquared
      malformedCell.original = false := by
  unfold GenericNI.cellCheck
  split
  · exact invalid_first_extreme_rejected _ _ _ _ firstWitnesses
  · rfl

theorem malformed_extreme_rejected :
    SubsetNI.check points radiusSquared malformedExtreme = false := by
  have hall : malformedExtreme.cells.all
      (fun cell => GenericNI.cellCheck cell.selected radiusSquared cell.original) = false := by
    change (GenericNI.cellCheck malformedCell.selected radiusSquared
      malformedCell.original && _) = false
    rw [malformed_cell_rejected]
    rfl
  simp only [SubsetNI.check, hall, Bool.and_false]

/-- The original accepted certificate covers every allowed orientation, including
endpoints.  This is a soundness consequence, not an external producer flag. -/
theorem original_all_directions (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) :
    ∃ selected : List DistanceLeaf.ExactPoint, selected ≠ [] ∧
      (∀ p ∈ selected, p ∈ points) ∧
      GenericNI.OrientationExcluded selected radiusSquared (NI.circleX t) (NI.circleY t) :=
  SubsetNI.check_orientation original_accepted t ht

/-- The same actual triangle containing the original points strictly enters the
open disk of the original squared radius, with no orientation hypothesis. -/
theorem original_strict_intrusion (T : UnitTriangle)
    (contained : ∀ p ∈ points, DistanceLeaf.toPlane p ∈ T.region) :
    ∃ p ∈ T.region, ‖p‖ ^ 2 < (radiusSquared : ℝ) :=
  SubsetNI.check_sound original_accepted T contained

#print axioms original_accepted
#print axioms original_identity
#print axioms missing_direction_rejected
#print axioms malformed_extreme_rejected
#print axioms other_extremes_preserved
#print axioms original_all_directions
#print axioms original_strict_intrusion
end HexagonCover.FinalNIControls
