import Mathlib

/-!
Exact rational interval operations, with soundness statements in the real numbers.
The endpoints remain rational; no floating-point computation enters these lemmas.
-/

namespace HexagonCover.Exact

structure Interval where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi

def Interval.Contains (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def singleton (q : ℚ) : Interval := ⟨q, q, le_rfl⟩

theorem singleton_contains (q : ℚ) : (singleton q).Contains (q : ℝ) :=
  ⟨le_rfl, le_rfl⟩

def add (I J : Interval) : Interval :=
  ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.ordered J.ordered⟩

theorem add_contains {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  constructor
  · simpa [add] using add_le_add hx.1 hy.1
  · simpa [add] using add_le_add hx.2 hy.2

def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo, neg_le_neg I.ordered⟩

theorem neg_contains {I : Interval} {x : ℝ}
    (hx : I.Contains x) : (neg I).Contains (-x) := by
  constructor
  · simpa [neg] using neg_le_neg hx.2
  · simpa [neg] using neg_le_neg hx.1

def sub (I J : Interval) : Interval := add I (neg J)

theorem sub_contains {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_contains hx (neg_contains hy)

theorem mul_lower {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (y : ℝ) :
    min (a * y) (b * y) ≤ x * y := by
  by_cases hy : 0 ≤ y
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hax hy)
  · exact (min_le_right _ _).trans
      (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hy))

theorem mul_upper {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (y : ℝ) :
    x * y ≤ max (a * y) (b * y) := by
  by_cases hy : 0 ≤ y
  · exact (mul_le_mul_of_nonneg_right hxb hy).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hax (le_of_not_ge hy)).trans (le_max_left _ _)

theorem product_bounds {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hal : min (a * c) (a * d) ≤ a * y := by
    simpa only [mul_comm] using mul_lower hy.1 hy.2 a
  have hbl : min (b * c) (b * d) ≤ b * y := by
    simpa only [mul_comm] using mul_lower hy.1 hy.2 b
  have hau : a * y ≤ max (a * c) (a * d) := by
    simpa only [mul_comm] using mul_upper hy.1 hy.2 a
  have hbu : b * y ≤ max (b * c) (b * d) := by
    simpa only [mul_comm] using mul_upper hy.1 hy.2 b
  constructor
  · exact (min_le_min hal hbl).trans (mul_lower hx.1 hx.2 y)
  · exact (mul_upper hx.1 hx.2 y).trans (max_le_max hau hbu)

def mul (I J : Interval) : Interval where
  lo := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  hi := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  ordered := by
    calc
      _ ≤ I.lo * J.lo := (min_le_left _ _).trans (min_le_left _ _)
      _ ≤ _ := (le_max_left _ _).trans (le_max_left _ _)

theorem mul_contains {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x * y) := by
  simpa [Interval.Contains, mul] using product_bounds hx hy

theorem square_upper {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    x ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
  by_cases h : x ≤ 0
  · have hp : 0 ≤ (x - a) * (-x - a) :=
      mul_nonneg (sub_nonneg.mpr hx.1) (by linarith [hx.1])
    have hs : x ^ 2 ≤ a ^ 2 := by nlinarith
    exact hs.trans (le_max_left _ _)
  · have hp : 0 ≤ (b - x) * (b + x) :=
      mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.2])
    have hs : x ^ 2 ≤ b ^ 2 := by nlinarith
    exact hs.trans (le_max_right _ _)

/-- The exact range of squaring a closed interval, including sign crossings. -/
def square (I : Interval) : Interval where
  lo := if 0 ≤ I.lo then I.lo ^ 2 else if I.hi ≤ 0 then I.hi ^ 2 else 0
  hi := max (I.lo ^ 2) (I.hi ^ 2)
  ordered := by
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
    · exact (sq_nonneg I.lo).trans (le_max_left _ _)

theorem square_contains {I : Interval} {x : ℝ}
    (hx : I.Contains x) : (square I).Contains (x ^ 2) := by
  constructor
  · change ((if 0 ≤ I.lo then I.lo ^ 2 else if I.hi ≤ 0 then I.hi ^ 2 else 0 : ℚ) : ℝ) ≤ x ^ 2
    split_ifs with hlo hhi
    · have hl : (0 : ℝ) ≤ I.lo := by exact_mod_cast hlo
      have hp : 0 ≤ (x - I.lo) * (x + I.lo) :=
        mul_nonneg (sub_nonneg.mpr hx.1) (by linarith [hx.1])
      push_cast
      nlinarith
    · have hh : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
      have hp : 0 ≤ (I.hi - x) * (-I.hi - x) :=
        mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.2])
      push_cast
      nlinarith
    · simpa using sq_nonneg x
  · simpa [square] using square_upper hx

/-- Reciprocal endpoints are valid precisely on intervals avoiding zero. -/
def reciprocal (I : Interval) (h : 0 < I.lo ∨ I.hi < 0) : Interval where
  lo := 1 / I.hi
  hi := 1 / I.lo
  ordered := by
    rcases h with h | h
    · exact one_div_le_one_div_of_le h I.ordered
    · exact one_div_le_one_div_of_neg_of_le h I.ordered

theorem reciprocal_contains {I : Interval} {x : ℝ}
    (h : 0 < I.lo ∨ I.hi < 0) (hx : I.Contains x) :
    (reciprocal I h).Contains (1 / x) := by
  rcases h with hlo | hhi
  · have hl : (0 : ℝ) < I.lo := by exact_mod_cast hlo
    have hp : 0 < x := hl.trans_le hx.1
    constructor
    · simpa [reciprocal] using one_div_le_one_div_of_le hp hx.2
    · simpa [reciprocal] using one_div_le_one_div_of_le hl hx.1
  · have hh : (I.hi : ℝ) < 0 := by exact_mod_cast hhi
    have hn : x < 0 := hx.2.trans_lt hh
    constructor
    · simpa [reciprocal] using one_div_le_one_div_of_neg_of_le hh hx.2
    · simpa [reciprocal] using one_div_le_one_div_of_neg_of_le hn hx.1

def divide (I J : Interval) (h : 0 < J.lo ∨ J.hi < 0) : Interval :=
  mul I (reciprocal J h)

theorem divide_contains {I J : Interval} {x y : ℝ}
    (h : 0 < J.lo ∨ J.hi < 0) (hx : I.Contains x) (hy : J.Contains y) :
    (divide I J h).Contains (x / y) := by
  simpa [divide, div_eq_mul_inv] using mul_contains hx (reciprocal_contains h hy)

end HexagonCover.Exact
