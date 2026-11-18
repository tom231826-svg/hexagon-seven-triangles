import HexagonCover.NBand.M6667_6700.ActualPacket
import HexagonCover.NBand.M6667_6700.Root

/-! The original M6667_6700 tree excludes its entire actual normalized no-gap
band. This is a branch of the larger covering argument, not its full theorem. -/
namespace HexagonCover.NBand.M6667_6700.ActualBand
open HexagonCover.Configuration NormalizedHeavy

theorem impossible {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i) (band : Parameters.Band h) : False :=
  Root.packet_impossible (SourceCoordinates.rotateConfig config)
    (SourceCoordinates.covered h.cover) (ActualPacket.conditions h nogaps band)

theorem impossible_of_bounds {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i)
    (lower : (2/3:ℝ) ≤ M h) (upper : M h ≤ (67/100:ℝ)) : False :=
  impossible h nogaps ⟨by simpa [Parameters.parameters] using lower,
    by simpa [Parameters.parameters] using upper⟩

#print axioms impossible
#print axioms impossible_of_bounds
end HexagonCover.NBand.M6667_6700.ActualBand
