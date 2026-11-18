import HexagonCover.SmallestN.ScalarBounds
import HexagonCover.SmallestN.MandatoryGeometry
import HexagonCover.SmallestN.BoundaryCoverage

/-! Every actual normalized no-gap cover in this band supplies the complete
original N packet conditions after one explicit whole-configuration rotation. -/
namespace HexagonCover.SmallestN.ActualPacket
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates
noncomputable section

theorem right_parameter_eq (i : Fin 6) :
    (MandatoryGeometry.rightParameter i : ℝ)=ScalarBounds.forwardLength i := by
  fin_cases i <;> norm_num [MandatoryGeometry.rightParameter,ScalarBounds.forwardLength]

theorem conditions {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (band : ScalarBounds.Band h) :
    Semantics.PacketConditions (rotateConfig config) where
  mandatory := by
    apply MandatoryGeometry.mandatory_of_geometry (rotateConfig config)
    · exact SourceCoordinates.anchors h.cover
    · intro i
      apply SourceCoordinates.left_endpoint h.cover i
      · norm_num [MandatoryGeometry.leftParameter]
      · simpa [MandatoryGeometry.leftParameter] using ScalarBounds.backward_lower h band i
    · intro i
      rw [right_parameter_eq]
      exact SourceCoordinates.right_endpoint h.cover i (ScalarBounds.forward_bounds i)
        (ScalarBounds.forward_lower h nogaps band i)
    · have hd := NPacketBounds.central_safe_radius h (U:=(83:ℝ)/100)
        (by norm_num) (by norm_num) band.upper
      convert hd using 1 <;> norm_num [MandatoryGeometry.centralRadius]
  outerCoverage := BoundaryCoverage.outerCoverage_of_noGap h.cover nogaps
  heavyNonIntrusion := by
    intro z hz
    have hs := NPacketBounds.heavy_radius_sq h (L:=(81:ℝ)/100) (by norm_num) band.lower z hz
    norm_num [Common.radiusSquared] at hs ⊢
    exact hs

end
end HexagonCover.SmallestN.ActualPacket
