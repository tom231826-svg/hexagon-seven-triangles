import HexagonCover.N7900.ActualPacket
import HexagonCover.N7900.SplitVerifiedRoot

/-! The original M7900_8100 tree excludes its entire actual normalized no-gap
band. This is a branch of the larger covering argument, not its full theorem. -/
namespace HexagonCover.N7900.SplitVerifiedActualBand
open Configuration NormalizedHeavy

theorem impossible {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i) (band : Parameters.Band h) : False :=
  SplitVerifiedRoot.packet_impossible (SourceCoordinates.rotateConfig config)
    (SourceCoordinates.covered h.cover) (ActualPacket.conditions h nogaps band)

theorem impossible_of_bounds {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i)
    (lower : (79:ℝ)/100 ≤ M h) (upper : M h ≤ (81:ℝ)/100) : False :=
  impossible h nogaps ⟨by simpa [Parameters.parameters] using lower,
    by simpa [Parameters.parameters] using upper⟩

#print axioms impossible
#print axioms impossible_of_bounds
end HexagonCover.N7900.SplitVerifiedActualBand
