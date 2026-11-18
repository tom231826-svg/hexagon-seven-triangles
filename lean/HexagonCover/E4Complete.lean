import HexagonCover.E4InsideActualSeam
import HexagonCover.E4T4Actual
import HexagonCover.E4Outside
import HexagonCover.GapExclusions

/-! Source-exposed continuous geometry closure of the nine positive-gap
families. The global covering theorem and its semantic audit are separate. -/
namespace HexagonCover.E4Complete
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates

theorem sole_impossible {config : Fin 7 → UnitTriangle}
    (h : Normalized config) (sole : ∀i,BoundaryGaps.gap h.cover i ↔ i=4) : False := by
  have hA := E4Outside.A_mem_two h sole
  have hthree := E4InsideActualSeam.actual_Pa_not_three h sole hA
  exact E4T4Actual.Pa_not_interior_four h sole
    (E4InsideOwners.actual_Pa_interior_four_of_not_three h sole hthree)

/-- An arbitrary actual normalized strict cover has no positive boundary gap.
No NI, active-angle, ownership or central-packet condition is added here. -/
theorem no_positive_gaps {config : Fin 7 → UnitTriangle}
    (h : Normalized config) : ∀i,¬BoundaryGaps.gap h.cover i := by
  intro i hg
  exact sole_impossible h (GapExclusions.only_edge4 h ⟨i,hg⟩)

#print axioms sole_impossible
#print axioms no_positive_gaps
end
end HexagonCover.E4Complete
