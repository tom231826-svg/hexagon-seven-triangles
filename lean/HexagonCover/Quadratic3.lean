import Mathlib

/-!+# Exact arithmetic in rational pairs for a + b √3

The executable operations use only rational arithmetic. `positive` compares
rational signs and squares. The real square root occurs only in the semantic
interpretation and the proofs of soundness, never in the computation.
-/

namespace HexagonCover.Quadratic3

abbrev Number := ℚ × ℚ

def ofRat (q : ℚ) : Number := (q, 0)

def add (x y : Number) : Number := (x.1 + y.1, x.2 + y.2)

def neg (x : Number) : Number := (-x.1, -x.2)

def sub (x y : Number) : Number := add x (neg y)

def mul (x y : Number) : Number :=
  (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

def square (x : Number) : Number := mul x x

noncomputable def real (x : Number) : ℝ :=
  (x.1 : ℝ) + (x.2 : ℝ) * Real.sqrt 3

@[simp] theorem real_ofRat (q : ℚ) : real (ofRat q) = q := by
  simp [real, ofRat]

@[simp] theorem real_add (x y : Number) : real (add x y) = real x + real y := by
  simp only [real, add, Rat.cast_add]
  ring

@[simp] theorem real_neg (x : Number) : real (neg x) = -real x := by
  simp only [real, neg, Rat.cast_neg]
  ring

@[simp] theorem real_sub (x y : Number) : real (sub x y) = real x - real y := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem real_mul (x y : Number) : real (mul x y) = real x * real y := by
  dsimp [real, mul]
  push_cast
  ring_nf
  rw [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]

@[simp] theorem real_square (x : Number) : real (square x) = real x ^ 2 := by
  simp [square, pow_two]

/-- A Boolean sign test using three rational sign cases. Both nonnegative
coefficients require one strict inequality. In opposite-sign cases the strict
squared inequality is decisive. Equality of squares does not certify positivity.
-/
def positive (x : Number) : Bool :=
  decide
    ((0 ≤ x.1 ∧ 0 ≤ x.2 ∧ (0 < x.1 ∨ 0 < x.2)) ∨
     (0 ≤ x.1 ∧ x.2 ≤ 0 ∧ 3 * x.2 ^ 2 < x.1 ^ 2) ∨
     (x.1 ≤ 0 ∧ 0 ≤ x.2 ∧ x.1 ^ 2 < 3 * x.2 ^ 2))

theorem sqrt_term_square (b : ℚ) :
    ((b : ℝ) * Real.sqrt 3) ^ 2 = 3 * (b : ℝ) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  ring

/-- A successful rational sign test implies strict positivity in ℝ. -/
theorem positive_sound (x : Number) (accepted : positive x = true) : 0 < real x := by
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (3 : ℝ) := le_of_lt hsqrt
  have hcases := of_decide_eq_true accepted
  change 0 < (x.1 : ℝ) + (x.2 : ℝ) * Real.sqrt 3
  rcases hcases with h | h | h
  · have ha : (0 : ℝ) ≤ x.1 := by exact_mod_cast h.1
    have hb : (0 : ℝ) ≤ x.2 := by exact_mod_cast h.2.1
    rcases h.2.2 with ha' | hb'
    · have haPos : (0 : ℝ) < x.1 := by exact_mod_cast ha'
      exact add_pos_of_pos_of_nonneg haPos (mul_nonneg hb hsqrt0)
    · have hbPos : (0 : ℝ) < x.2 := by exact_mod_cast hb'
      exact add_pos_of_nonneg_of_pos ha (mul_pos hbPos hsqrt)
  · have ha : (0 : ℝ) ≤ x.1 := by exact_mod_cast h.1
    have hb : (x.2 : ℝ) ≤ 0 := by exact_mod_cast h.2.1
    have hsq : 3 * (x.2 : ℝ) ^ 2 < (x.1 : ℝ) ^ 2 := by
      exact_mod_cast h.2.2
    have hterm : (x.2 : ℝ) * Real.sqrt 3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hb hsqrt0
    have hsq' : (-((x.2 : ℝ) * Real.sqrt 3)) ^ 2 < (x.1 : ℝ) ^ 2 := by
      simpa only [neg_sq, sqrt_term_square] using hsq
    have hlt := (sq_lt_sq₀ (neg_nonneg.mpr hterm) ha).mp hsq'
    linarith
  · have ha : (x.1 : ℝ) ≤ 0 := by exact_mod_cast h.1
    have hb : (0 : ℝ) ≤ x.2 := by exact_mod_cast h.2.1
    have hsq : (x.1 : ℝ) ^ 2 < 3 * (x.2 : ℝ) ^ 2 := by
      exact_mod_cast h.2.2
    have hterm : 0 ≤ (x.2 : ℝ) * Real.sqrt 3 := mul_nonneg hb hsqrt0
    have hsq' : (-(x.1 : ℝ)) ^ 2 < ((x.2 : ℝ) * Real.sqrt 3) ^ 2 := by
      simpa only [neg_sq, sqrt_term_square] using hsq
    have hlt := (sq_lt_sq₀ (neg_nonneg.mpr ha) hterm).mp hsq'
    linarith

end HexagonCover.Quadratic3
