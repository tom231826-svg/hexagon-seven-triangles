import HexagonCover.NBand.M7300_7500.ActualPacket
import HexagonCover.NBand.M7300_7500.Root

/-! The original M7300_7500 tree excludes its entire actual normalized no-gap
band. This is a branch of the larger covering argument, not its full theorem. -/
namespace HexagonCover.NBand.M7300_7500.ActualBand
open HexagonCover.Configuration NormalizedHeavy

theorem impossible {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i) (band : Parameters.Band h) : False :=
  Root.packet_impossible (SourceCoordinates.rotateConfig config)
    (SourceCoordinates.covered h.cover) (ActualPacket.conditions h nogaps band)

theorem impossible_of_bounds {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i)
    (lower : (73/100:ℝ) ≤ M h) (upper : M h ≤ (3/4:ℝ)) : False :=
  impossible h nogaps ⟨by simpa [Parameters.parameters] using lower,
    by simpa [Parameters.parameters] using upper⟩

#print axioms impossible
#print axioms impossible_of_bounds
end HexagonCover.NBand.M7300_7500.ActualBand
