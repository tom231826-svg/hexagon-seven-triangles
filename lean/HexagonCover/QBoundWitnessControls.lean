import HexagonCover.QBoundWitness
import HexagonCover.DistanceData.Batch0000
import HexagonCover.SupportQData.Wave002Rows0000
import HexagonCover.QNIData.Batch0000

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace HexagonCover.QBoundWitnessControls
open DistanceData QCertificate QBoundWitness

def diameter : Row .q25 := ⟨0, false, 0, ([0] : List (Fin 253))⟩
def segment : Row .q25 := ⟨174, true, 2, ([47] : List (Fin 253))⟩
def support : Row .q25 := ⟨1131, false, 4, ([69,84,100,101,117,188,242,245] : List (Fin 253))⟩
def interval : Row .q25 := ⟨1021, false, 2, ([0,7,16] : List (Fin 253))⟩

theorem diameter_resolved : Resolved diameter :=
  fromDiameter DistanceData.Batch0000.w00000 rfl rfl

theorem segment_resolved : Resolved segment :=
  fromSegment PointSegmentData.w0000 rfl rfl rfl (Or.inr rfl)

theorem support_resolved : Resolved support :=
  fromSupport SupportQData.Wave002Rows0000.w000106 rfl rfl

theorem interval_resolved : Resolved interval :=
  fromInterval QNIData.Batch0000.c0000_row0000 rfl rfl rfl rfl (Or.inr rfl)

theorem wrong_owner_key :
    key { interval with owner := 5 } ≠ key interval := by decide +kernel
theorem wrong_flag_key :
    key { interval with originalFlag := true } ≠ key interval := by decide +kernel
def wrongIdsRow : Row .q25 := { interval with points := ([0,7,17] : List (Fin 253)) }
theorem wrong_ids_key :
    key wrongIdsRow ≠ key interval := by
  decide +kernel
theorem wrong_radius :
    (QNIData.Batch0000.c0000_row0000.data.radiusSquared : ℚ) ≠ (1 / 4) ^ 2 := by
  decide +kernel

#print axioms diameter_resolved
#print axioms segment_resolved
#print axioms support_resolved
#print axioms interval_resolved
end HexagonCover.QBoundWitnessControls
