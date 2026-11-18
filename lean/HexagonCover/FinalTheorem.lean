import HexagonCover.E4Complete
import HexagonCover.NVerifiedBands
import HexagonCover.HighMUpper

/-! Final assembly for the original seven-triangle covering statement.
The normalized strict cover is derived from any hypothetical expanded cover;
it is not retained as a hypothesis in `cover_conjecture` or `no_seven_cover`.
Independent replay and semantic/reproducibility audits are tracked separately.
-/
namespace HexagonCover.FinalTheorem
noncomputable section
open HexagonCover.Configuration NormalizedHeavy

theorem low_high_overlap : NICertificate.halfRoot < (87:ℝ)/100 := by
  have hh := ExtremeTriangle.halfRoot_pos
  nlinarith only [ExtremeTriangle.halfRoot_sq,hh]

theorem normalized_impossible {config : Fin 7 → UnitTriangle}
    (h : Normalized config) : False := by
  have nogaps := E4Complete.no_positive_gaps h
  by_cases hlow : M h ≤ (87:ℝ)/100
  · exact NVerifiedBands.impossible_of_upper h nogaps hlow
  · exact HighMUpper.impossible h nogaps
      (le_trans low_high_overlap.le (le_of_not_ge hlow))

theorem strict_cover_impossible (config : Fin 7 → UnitTriangle) :
    ¬StrictCover config := by
  intro h
  obtain ⟨action,hnormal⟩ := exists_normalized h
  exact normalized_impossible hnormal

/-- Exactly the target proposition from Geometry, with no auxiliary geometric
or computational assumptions. -/
theorem cover_conjecture : CoverConjecture :=
  target_of_strict_cover_exclusion strict_cover_impossible

/-- Explicit quantified form of the original statement. -/
theorem no_seven_cover (s : ℝ) (hs : 1<s) (config : Fin 7 → UnitTriangle) :
    ¬Covers s config := cover_conjecture s hs config

/-- The boundary size is achievable, including an allowed repeated piece. -/
theorem size_one_is_covered : ∃config : Fin 7 → UnitTriangle,Covers 1 config :=
  StandardCover.exists_unit_hexagon_cover

#print axioms normalized_impossible
#print axioms strict_cover_impossible
#print axioms cover_conjecture
#print axioms no_seven_cover
#print axioms size_one_is_covered
end
end HexagonCover.FinalTheorem
