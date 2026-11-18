import HexagonCover.Ranges
import HexagonCover.NBand.M6667_6700.ActualBand
import HexagonCover.NBand.M6700_6900.ActualBand
import HexagonCover.NBand.M6900_7100.ActualBand
import HexagonCover.NBand.M7100_7300.ActualBand
import HexagonCover.NBand.M7300_7500.ActualBand
import HexagonCover.NBand.M7500_7700.ActualBand
import HexagonCover.NBand.M7700_7900.ActualBand
import HexagonCover.N7900.SplitVerifiedActualBand
import HexagonCover.SmallestN.ActualBand
import HexagonCover.NBand.M8300_8500.ActualBand
import HexagonCover.NBand.M8500_8700.ActualBand

namespace HexagonCover.NVerifiedBands
open NormalizedHeavy

/-- The eleven original low-reach certificates exclude the given normalized no-gap cover. -/
theorem impossible_of_upper {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀ i, ¬BoundaryGaps.gap h.cover i)
    (upper : M h ≤ (87 : ℝ) / 100) : False := by
  have lower : (2 : ℝ) / 3 ≤ M h := (structure_bounds h).2.2.2.1.le
  obtain ⟨b, hb, hbM⟩ := Ranges.low_band_coverage lower upper
  simp only [Ranges.lowBands, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Ranges.InBand] at hbM
  · exact NBand.M6667_6700.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact NBand.M6700_6900.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact NBand.M6900_7100.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact NBand.M7100_7300.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact NBand.M7300_7500.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact NBand.M7500_7700.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact NBand.M7700_7900.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact N7900.SplitVerifiedActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact SmallestN.ActualBand.impossible h nogaps ⟨hbM.1, hbM.2⟩
  · exact NBand.M8300_8500.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2
  · exact NBand.M8500_8700.ActualBand.impossible_of_bounds h nogaps hbM.1 hbM.2

#print axioms impossible_of_upper
end HexagonCover.NVerifiedBands
