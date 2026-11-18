import HexagonCover.NBand.M6667_6700.Parameters
import HexagonCover.NBand.M6667_6700.BoundaryCoverage

/-! All original packet conditions follow for one actual normalized no-gap
configuration in this band, after the explicit whole-configuration rotation. -/
namespace HexagonCover.NBand.M6667_6700.ActualPacket
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates Parameters
noncomputable section

theorem conditions {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i) (band : Band h) :
    Semantics.PacketConditions (rotateConfig config) where
  mandatory := by
    apply MandatoryGeometry.mandatory_of_geometry (rotateConfig config)
    · exact SourceCoordinates.anchors h.cover
    · intro i
      apply SourceCoordinates.left_endpoint h.cover i
      · norm_num [MandatoryGeometry.leftParameter]
      · rw [left_parameter_eq]
        exact NPacketParameters.backward_lower parameters h band i
    · intro i
      rw [right_parameter_eq]
      exact SourceCoordinates.right_endpoint h.cover i
        (NPacketParameters.forward_bounds guards i)
        (NPacketParameters.forward_lower guards h nogaps band i)
    · rw [central_radius_eq]
      exact NPacketParameters.central_disk guards h band
  outerCoverage := BoundaryCoverage.outerCoverage_of_noGap h.cover nogaps
  heavyNonIntrusion := by
    intro z hz
    rw [authoritative_radius_eq]
    exact NPacketParameters.heavy_radius_sq guards h band z hz

#print axioms conditions
end
end HexagonCover.NBand.M6667_6700.ActualPacket
