import HexagonCover.CentralBoundary

/-! Actual positive boundary gaps belong to the same central triangle,
including both endpoints by closedness. Gap equality means no positive gap. -/
namespace HexagonCover.BoundaryGaps
open HexagonCover.Configuration BoundaryOwners CentralBoundary
noncomputable section

def gap {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) : Prop :=
  b h i + a h (i+1) < 1

theorem reversed_edge (i : Fin 6) (t : ℝ) : edgePoint i t =
    AffineMap.lineMap (hexVertex 1 (i+1)) (hexVertex 1 ((i+1)-1)) (1-t) := by
  rw [add_sub_cancel_right]
  simp only [edgePoint, AffineMap.lineMap_apply_module]
  module

theorem open_gap_central {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) {t : ℝ}
    (ht : t ∈ Set.Ioo (b h i) (1-a h (i+1))) :
    edgePoint i t ∈ (config 6).region := by
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 := by
    have hb := (rightReach h i).positive
    have ha := (leftReach h (i+1)).positive
    change 0 < b h i at hb
    change 0 < a h (i+1) at ha
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rcases actual_three_owners h i ht01 with hleft | hright | hc
  · have hle := ((rightReach h i).character t ht01).mp hleft
    change t ≤ b h i at hle
    exact (not_le.mpr ht.1 hle).elim
  · have ht' : 1-t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht01.2], by linarith [ht01.1]⟩
    rw [reversed_edge] at hright
    have hle := ((leftReach h (i+1)).character (1-t) ht').mp hright
    change 1-t ≤ a h (i+1) at hle
    have : a h (i+1) < 1-t := by linarith [ht.2]
    exact (not_le.mpr this hle).elim
  · exact hc

theorem closed_gap_central {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hi : gap h i) :
    ∀ t ∈ Set.Icc (b h i) (1-a h (i+1)), edgePoint i t ∈ (config 6).region := by
  have hclosed : IsClosed ((edgePoint i) ⁻¹' (config 6).region) :=
    (config 6).closed_region.preimage
      (lipschitzWith_lineMap (𝕜 := ℝ) (hexVertex 1 i) (hexVertex 1 (i+1))).continuous
  have hsub : Set.Ioo (b h i) (1-a h (i+1)) ⊆ (edgePoint i) ⁻¹' (config 6).region := by
    intro t ht
    exact open_gap_central h i ht
  have hc := hclosed.closure_subset_iff.mpr hsub
  have hr : b h i < 1-a h (i+1) := by change b h i + a h (i+1) < 1 at hi; linarith
  rw [closure_Ioo hr.ne] at hc
  exact hc

theorem gap_implies_contact {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hi : gap h i) : touches h i := by
  have hb0 := (rightReach h i).positive
  have hb1 := (rightReach h i).lt_one
  have hba : b h i ≤ 1-a h (i+1) := by change b h i + a h (i+1) < 1 at hi; linarith
  exact ⟨b h i, ⟨hb0.le, hb1.le⟩, closed_gap_central h i hi _ ⟨le_rfl, hba⟩⟩

theorem all_gaps_in_adjacent_pair {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) : ∃ k : Fin 6, ∀ i, gap h i → i=k ∨ i=k+1 := by
  obtain ⟨k, hk⟩ := all_contacts_in_adjacent_pair h
  exact ⟨k, fun i hi => hk i (gap_implies_contact h i hi)⟩

def ninePatterns : List (Finset (Fin 6)) :=
  [{0},{1},{2},{3},{0,1},{1,2},{2,3},{4},{3,4}]

theorem finite_pattern_classification : ∀ S : Finset (Fin 6), S.Nonempty → 5 ∉ S →
    (∃ k : Fin 6, ∀ i ∈ S, i=k ∨ i=k+1) → S ∈ ninePatterns := by
  decide +kernel

/-- The no-gap condition on edge5 is a separate explicit geometric premise,
to be discharged after normalizing the unique heavy NI piece. -/
theorem positive_gap_nine_patterns {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (nonempty : ∃ i, gap h i) (edge5 : ¬ gap h 5) :
    ∃ S ∈ ninePatterns, ∀ i, gap h i ↔ i ∈ S := by
  classical
  let S := Finset.univ.filter (gap h)
  have hS (i : Fin 6) : i ∈ S ↔ gap h i := by simp [S]
  have hn : S.Nonempty := by obtain ⟨i, hi⟩ := nonempty; exact ⟨i, (hS i).mpr hi⟩
  have h5 : (5 : Fin 6) ∉ S := fun hh => edge5 ((hS 5).mp hh)
  obtain ⟨k, hk⟩ := all_gaps_in_adjacent_pair h
  have hc : ∃ k : Fin 6, ∀ i ∈ S, i=k ∨ i=k+1 :=
    ⟨k, fun i hi => hk i ((hS i).mp hi)⟩
  exact ⟨S, finite_pattern_classification S hn h5 hc, fun i => (hS i).symm⟩

end
end HexagonCover.BoundaryGaps
