import Mathlib

/-!
Scalar algebra used by the normalized-infeasibility formulation. These lemmas
establish the circle chart and strict convexity facts independently of any
finite branch certificate.
-/

namespace HexagonCover.NI

noncomputable def circleX (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
noncomputable def circleY (t : ℝ) : ℝ := (2 * t) / (1 + t ^ 2)

theorem circle_den_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem circle_unit (t : ℝ) : (circleX t) ^ 2 + (circleY t) ^ 2 = 1 := by
  unfold circleX circleY
  field_simp [ne_of_gt (circle_den_pos t)]
  ring

theorem circleX_nonneg {t : ℝ} (ht : -1 ≤ t ∧ t ≤ 1) : 0 ≤ circleX t := by
  unfold circleX
  apply div_nonneg _ (le_of_lt (circle_den_pos t))
  have hp : 0 ≤ (1 - t) * (1 + t) := mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
  nlinarith

theorem chart_den_pos {c d : ℝ} (_hunit : c ^ 2 + d ^ 2 = 1) (hc : 0 ≤ c) :
    0 < 1 + c := by linarith

theorem chart_mem {c d : ℝ} (hunit : c ^ 2 + d ^ 2 = 1) (hc : 0 ≤ c) :
    -1 ≤ d / (1 + c) ∧ d / (1 + c) ≤ 1 := by
  have hp : 0 < 1 + c := chart_den_pos hunit hc
  have hdlo : -1 ≤ d := by nlinarith [sq_nonneg c]
  have hdhi : d ≤ 1 := by nlinarith [sq_nonneg c]
  constructor
  · apply (le_div_iff₀ hp).2
    nlinarith
  · apply (div_le_iff₀ hp).2
    nlinarith

theorem chart_reconstruct_x {c d : ℝ}
    (hunit : c ^ 2 + d ^ 2 = 1) (hc : 0 ≤ c) :
    circleX (d / (1 + c)) = c := by
  have hp : 1 + c ≠ 0 := ne_of_gt (chart_den_pos hunit hc)
  have hq : 1 + (d / (1 + c)) ^ 2 ≠ 0 := ne_of_gt (circle_den_pos _)
  unfold circleX
  apply (div_eq_iff hq).2
  field_simp [hp]
  nlinarith [congrArg (fun z : ℝ => c * z) hunit]

theorem chart_reconstruct_y {c d : ℝ}
    (hunit : c ^ 2 + d ^ 2 = 1) (hc : 0 ≤ c) :
    circleY (d / (1 + c)) = d := by
  have hp : 1 + c ≠ 0 := ne_of_gt (chart_den_pos hunit hc)
  have hq : 1 + (d / (1 + c)) ^ 2 ≠ 0 := ne_of_gt (circle_den_pos _)
  unfold circleY
  apply (div_eq_iff hq).2
  field_simp [hp]
  nlinarith [congrArg (fun z : ℝ => d * z) hunit]

/-- Every point of the closed right semicircle occurs in the bounded chart. -/
theorem semicircle_parameterization {c d : ℝ}
    (hunit : c ^ 2 + d ^ 2 = 1) (hc : 0 ≤ c) :
    ∃ t : ℝ, (-1 ≤ t ∧ t ≤ 1) ∧ circleX t = c ∧ circleY t = d := by
  exact ⟨d / (1 + c), chart_mem hunit hc,
    chart_reconstruct_x hunit hc, chart_reconstruct_y hunit hc⟩

def normSq (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

theorem normSq_nonneg (x y : ℝ) : 0 ≤ normSq x y := by
  unfold normSq
  positivity

/-- The exact three-point variance identity, before normalizing the weights. -/
theorem weighted_variance (a b c x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) :
    (a + b + c) * (a * normSq x₁ y₁ + b * normSq x₂ y₂ + c * normSq x₃ y₃) -
      normSq (a * x₁ + b * x₂ + c * x₃) (a * y₁ + b * y₂ + c * y₃) =
      a * b * normSq (x₁ - x₂) (y₁ - y₂) +
        a * c * normSq (x₁ - x₃) (y₁ - y₃) +
        b * c * normSq (x₂ - x₃) (y₂ - y₃) := by
  unfold normSq
  ring

theorem three_point_closed_bound
    {a b c x₁ y₁ x₂ y₂ x₃ y₃ r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (h₁ : normSq x₁ y₁ ≤ r) (h₂ : normSq x₂ y₂ ≤ r) (h₃ : normSq x₃ y₃ ≤ r) :
    normSq (a * x₁ + b * x₂ + c * x₃) (a * y₁ + b * y₂ + c * y₃) ≤ r := by
  have hbudget : a * normSq x₁ y₁ + b * normSq x₂ y₂ + c * normSq x₃ y₃ ≤ r := by
    calc
      _ ≤ a * r + b * r + c * r :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ ha)
          (mul_le_mul_of_nonneg_left h₂ hb)) (mul_le_mul_of_nonneg_left h₃ hc)
      _ = (a + b + c) * r := by ring
      _ = r := by rw [hsum, one_mul]
  have hab : 0 ≤ a * b * normSq (x₁ - x₂) (y₁ - y₂) :=
    mul_nonneg (mul_nonneg ha hb) (normSq_nonneg _ _)
  have hac : 0 ≤ a * c * normSq (x₁ - x₃) (y₁ - y₃) :=
    mul_nonneg (mul_nonneg ha hc) (normSq_nonneg _ _)
  have hbc : 0 ≤ b * c * normSq (x₂ - x₃) (y₂ - y₃) :=
    mul_nonneg (mul_nonneg hb hc) (normSq_nonneg _ _)
  have hvariance := weighted_variance a b c x₁ y₁ x₂ y₂ x₃ y₃
  rw [hsum, one_mul] at hvariance
  linarith

/-- All weights may vanish individually: strictness comes from all three inputs. -/
theorem three_point_strict_bound
    {a b c x₁ y₁ x₂ y₂ x₃ y₃ r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (h₁ : normSq x₁ y₁ < r) (h₂ : normSq x₂ y₂ < r) (h₃ : normSq x₃ y₃ < r) :
    normSq (a * x₁ + b * x₂ + c * x₃) (a * y₁ + b * y₂ + c * y₃) < r := by
  let m := max (max (normSq x₁ y₁) (normSq x₂ y₂)) (normSq x₃ y₃)
  have h₁m : normSq x₁ y₁ ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have h₂m : normSq x₂ y₂ ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have h₃m : normSq x₃ y₃ ≤ m := le_max_right _ _
  have hmr : m < r := max_lt (max_lt h₁ h₂) h₃
  exact (three_point_closed_bound ha hb hc hsum h₁m h₂m h₃m).trans_lt hmr

/-- Positive mass on two distinct points makes the barycenter strictly interior. -/
theorem three_point_open_disk
    {a b c x₁ y₁ x₂ y₂ x₃ y₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (h₁ : normSq x₁ y₁ ≤ 1) (h₂ : normSq x₂ y₂ ≤ 1) (h₃ : normSq x₃ y₃ ≤ 1)
    (hsep : 0 < normSq (x₁ - x₂) (y₁ - y₂)) :
    normSq (a * x₁ + b * x₂ + c * x₃) (a * y₁ + b * y₂ + c * y₃) < 1 := by
  have hbudget : a * normSq x₁ y₁ + b * normSq x₂ y₂ + c * normSq x₃ y₃ ≤ 1 := by
    calc
      _ ≤ a * 1 + b * 1 + c * 1 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ ha.le)
          (mul_le_mul_of_nonneg_left h₂ hb.le)) (mul_le_mul_of_nonneg_left h₃ hc)
      _ = 1 := by simpa using hsum
  have hstrict : 0 < a * b * normSq (x₁ - x₂) (y₁ - y₂) :=
    mul_pos (mul_pos ha hb) hsep
  have hac : 0 ≤ a * c * normSq (x₁ - x₃) (y₁ - y₃) :=
    mul_nonneg (mul_nonneg ha.le hc) (normSq_nonneg _ _)
  have hbc : 0 ≤ b * c * normSq (x₂ - x₃) (y₂ - y₃) :=
    mul_nonneg (mul_nonneg hb.le hc) (normSq_nonneg _ _)
  have hvariance := weighted_variance a b c x₁ y₁ x₂ y₂ x₃ y₃
  rw [hsum, one_mul] at hvariance
  linarith

end HexagonCover.NI
