import HexagonCover.SmallestN.ActualPacket
import HexagonCover.SmallestN.Root

/-! The complete smallest frozen N interval is excluded for an actual
normalized no-gap configuration. Other M intervals and positive gaps remain
separate obligations; this is not the full CoverConjecture. -/
namespace HexagonCover.SmallestN.ActualBand
open Configuration NormalizedHeavy

theorem impossible {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (band : ScalarBounds.Band h) : False :=
  Root.packet_impossible (SourceCoordinates.rotateConfig config)
    (SourceCoordinates.covered h.cover) (ActualPacket.conditions h nogaps band)

#print axioms impossible
end HexagonCover.SmallestN.ActualBand
