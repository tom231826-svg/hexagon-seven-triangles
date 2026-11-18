import HexagonCover.Quadratic3

/-! Completeness of the exact sign test, needed for executable support maxima.
The original one-way arithmetic soundness module is unchanged. -/
namespace HexagonCover.Quadratic3

theorem positive_complete (x : Number) (hpos : 0 < real x) : positive x = true := by
  apply decide_eq_true
  have haR : (x.1 : ℝ) + (x.2 : ℝ) * Real.sqrt 3 > 0 := hpos
  have hr : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  by_cases ha : 0 ≤ x.1
  · have ha' : (0 : ℝ) ≤ x.1 := by exact_mod_cast ha
    by_cases hb : 0 ≤ x.2
    · have hp : 0 < x.1 ∨ 0 < x.2 := by
        by_contra hn
        push_neg at hn
        have hza : x.1 = 0 := le_antisymm hn.1 ha
        have hzb : x.2 = 0 := le_antisymm hn.2 hb
        simp [real, hza, hzb] at hpos
      exact Or.inl ⟨ha, hb, hp⟩
    · have hb0 : x.2 ≤ 0 := le_of_lt (lt_of_not_ge hb)
      have hb' : (x.2 : ℝ) ≤ 0 := by exact_mod_cast hb0
      have ht : (x.2 : ℝ) * Real.sqrt 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb' hr
      have hd : 0 < (x.1 : ℝ) - (x.2 : ℝ) * Real.sqrt 3 := by linarith
      have hm := mul_pos haR hd
      have hs : 3 * (x.2 : ℝ)^2 < (x.1 : ℝ)^2 := by
        nlinarith [sqrt_term_square x.2]
      exact Or.inr (Or.inl ⟨ha, hb0, by exact_mod_cast hs⟩)
  · have ha0 : x.1 ≤ 0 := le_of_lt (lt_of_not_ge ha)
    have ha' : (x.1 : ℝ) ≤ 0 := by exact_mod_cast ha0
    by_cases hb : 0 ≤ x.2
    · have hb' : (0 : ℝ) ≤ x.2 := by exact_mod_cast hb
      have hd : 0 < (x.2 : ℝ) * Real.sqrt 3 - (x.1 : ℝ) := by linarith
      have hm := mul_pos haR hd
      have hs : (x.1 : ℝ)^2 < 3 * (x.2 : ℝ)^2 := by
        nlinarith [sqrt_term_square x.2]
      exact Or.inr (Or.inr ⟨ha0, hb, by exact_mod_cast hs⟩)
    · have hb' : (x.2 : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (lt_of_not_ge hb)
      have ht := mul_nonpos_of_nonpos_of_nonneg hb' hr
      linarith

theorem positive_iff (x : Number) : positive x = true ↔ 0 < real x :=
  ⟨positive_sound x, positive_complete x⟩

def maximum (x y : Number) : Number := if positive (sub y x) then y else x

theorem real_maximum (x y : Number) : real (maximum x y) = max (real x) (real y) := by
  by_cases hp : positive (sub y x) = true
  · have hl := positive_sound _ hp
    rw [real_sub] at hl
    simp only [maximum, hp, ↓reduceIte]
    exact (max_eq_right (by linarith)).symm
  · have hl : real y ≤ real x := by
      by_contra hn
      have ht : 0 < real (sub y x) := by rw [real_sub]; linarith
      exact hp (positive_complete _ ht)
    simp only [maximum, hp, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_left hl).symm

end HexagonCover.Quadratic3
