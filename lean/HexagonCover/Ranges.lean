import Mathlib

/-! Exact coverage of the frozen low-M and high-M domains. No exclusion theorem
is assumed or proved by an interval-union identity. -/
namespace HexagonCover.Ranges

def lowBands : List (ℚ × ℚ) :=
  [(2/3,67/100),(67/100,69/100),(69/100,71/100),(71/100,73/100),
   (73/100,3/4),(3/4,77/100),(77/100,79/100),(79/100,81/100),
   (81/100,83/100),(83/100,17/20),(17/20,87/100)]

def InBand (x : ℝ) (b : ℚ × ℚ) : Prop := (b.1 : ℝ) ≤ x ∧ x ≤ (b.2 : ℝ)

theorem low_band_coverage {x : ℝ} (hlo : 2/3 ≤ x) (hhi : x ≤ 87/100) :
    ∃ b ∈ lowBands, InBand x b := by
  by_contra h
  simp only [lowBands, List.mem_cons, List.mem_singleton, exists_eq_or_imp] at h
  norm_num [InBand] at h
  rcases h with ⟨h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀⟩
  have h0 := h₀ hlo
  have h1 := h₁ (le_of_lt h0)
  have h2 := h₂ (le_of_lt h1)
  have h3 := h₃ (le_of_lt h2)
  have h4 := h₄ (le_of_lt h3)
  have h5 := h₅ (le_of_lt h4)
  have h6 := h₆ (le_of_lt h5)
  have h7 := h₇ (le_of_lt h6)
  have h8 := h₈ (le_of_lt h7)
  have h9 := h₉ (le_of_lt h8)
  have h10 := h₁₀ (le_of_lt h9)
  linarith

theorem exact_overlap : Real.sqrt 3 / 2 < (87/100 : ℝ) := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem full_parameter_coverage {M : ℝ} (hlo : 2/3 < M) (hhi : M < 1) :
    (∃ b ∈ lowBands, InBand M b) ∨
    (Real.sqrt 3 / 2 ≤ M ∧ M < 9/10) ∨
    (9/10 ≤ M ∧ M < 19/20) ∨
    (19/20 ≤ M ∧ M < 1) := by
  by_cases hlow : M ≤ 87/100
  · exact Or.inl (low_band_coverage (le_of_lt hlo) hlow)
  · have hM : Real.sqrt 3 / 2 ≤ M := by linarith [exact_overlap]
    right
    by_cases hmid : M < 9/10
    · exact Or.inl ⟨hM,hmid⟩
    · right
      by_cases htop : M < 19/20
      · exact Or.inl ⟨le_of_not_gt hmid,htop⟩
      · exact Or.inr ⟨le_of_not_gt htop,hhi⟩

end HexagonCover.Ranges
