import HexagonCover.SmallestN.Boundary
import HexagonCover.SmallestN.Semantics
import HexagonCover.NoGap

namespace HexagonCover.SmallestN.BoundaryCoverage

/-- The original outer-only owner restrictions follow from actual no-gap side
coverage, after the explicit physical rotation into the N source convention. -/
theorem outerCoverage_of_noGap {config : Fin 7 → UnitTriangle}
    (h : Configuration.StrictCover config)
    (nogaps : ∀ i, ¬ BoundaryGaps.gap h i) :
    ∀ p : Fin 170, Common.allowed p 6 = false →
      ∃ owner : Fin 7, owner.val < 6 ∧
        Semantics.Owns (SourceCoordinates.rotateConfig config) owner p := by
  intro p hp
  obtain ⟨ht, heq⟩ := Boundary.restricted_on_edge p hp
  obtain ⟨j, hj⟩ := NoGap.source_outer_edge_covered h nogaps (Boundary.edge p) ht
  exact ⟨j.castSucc, j.isLt, by simpa only [Semantics.Owns, heq] using hj⟩

#print axioms outerCoverage_of_noGap
end HexagonCover.SmallestN.BoundaryCoverage
