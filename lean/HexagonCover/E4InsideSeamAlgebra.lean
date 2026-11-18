import HexagonCover.E4InsidePositive

/-! Source-exposed exact T3-cap algebra from the final negative-r2 closure.
These are scalar consequences of the three SAME-T3 necessary inequalities;
their extraction from actual T3's active sides remains a geometric dependency. -/
namespace HexagonCover.E4InsideSeamAlgebra
noncomputable section

theorem deficit_bound {d S : ℝ} (hd : 0 < d) (hd1 : d < 1/2)
    (hS : 0 ≤ S) (hsq : S^2=1-d+d^2) :
    0 < 1-S ∧ d*(2-d) < 4*(1-S)*(1+d) := by
  have hprod := mul_pos hd (show 0 < 1-d by linarith)
  have hS1 : S < 1 := by nlinarith
  have hR : 0 < 1-S := by linarith
  have hhalf : d*(1-d) < 2*(1-S) := by nlinarith [sq_pos_of_pos hR]
  have hm := mul_lt_mul_of_pos_right hhalf (show 0 < 2*(1+d) by linarith)
  have hp := mul_pos (sq_pos_of_pos hd) (show 0 < 1-2*d by linarith)
  exact ⟨hR,by nlinarith only [hm,hp]⟩

/-- The source's sharpened cap follows from Pa's two actual T3 rows and the
strict same-T3 margin budget, before consulting T2's direction. -/
theorem t3_short_reach_cap {a a3 b3 d S : ℝ}
    (hd : 0 < d) (hd1 : d < 1/2) (hS : 0 ≤ S) (hsq : S^2=1-d+d^2)
    (hbudget : a3+b3 < S)
    (hP1 : 1-a/2-(1-a)*d ≤ b3)
    (hP2 : -a/2+(1-a/2)*d ≤ a3) :
    a3 < a/2+(1+a)*d/2 := by
  obtain ⟨hR,hbound⟩ := deficit_bound hd hd1 hS hsq
  by_contra hn
  have hfail : a/2+(1+a)*d/2 ≤ a3 := le_of_not_gt hn
  have hfirst : 2*(1-S) < (1-3*a)*d := by nlinarith only [hbudget,hP1,hfail]
  have hsecond : 1-S < a*(1-d/2) := by nlinarith only [hbudget,hP1,hP2]
  have hm1 := mul_lt_mul_of_pos_right hfirst (show 0 < 1-d/2 by linarith)
  have hm2 := mul_lt_mul_of_pos_left hsecond (show 0 < 3*d by linarith)
  nlinarith only [hm1,hm2,hbound]

theorem t3_height_cap {a a3 b3 d S : ℝ}
    (hd : 0 < d) (hd1 : d < 1/2) (hS : 0 ≤ S) (hsq : S^2=1-d+d^2)
    (hbudget : a3+b3 < S)
    (hP1 : 1-a/2-(1-a)*d ≤ b3)
    (hP2 : -a/2+(1-a/2)*d ≤ a3) :
    2*(a3+1/4-d/4)/(1+d)-1 < a-1/2 := by
  have hcap := t3_short_reach_cap hd hd1 hS hsq hbudget hP1 hP2
  have hden : 0 < 1+d := by linarith
  have hh : 2*(a3+1/4-d/4)/(1+d) < a+1/2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hcap]
  linarith

/-- Both nonnegative forward-exit cases and their tie share this budget.
At r=0 the strictly positive unused actual margin supplies strictness. -/
theorem nonnegative_t2_impossible {a a3 b3 d S s b r D d2 e2 : ℝ}
    (hd : 0 < d) (hd1 : d < 1/2) (hS : 0 ≤ S) (hsq : S^2=1-d+d^2)
    (hbudget : a3+b3 < S)
    (hP1 : 1-a/2-(1-a)*d ≤ b3) (hP2 : -a/2+(1-a/2)*d ≤ a3)
    (ha3 : 0 ≤ a3) (ha31 : a3 < 1/3) (hs : a/2 < s)
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hDsq : D^2=1+r+r^2)
    (hmargins : s+d2+e2=D) (hd2 : 0 < d2)
    (hforward : r*b ≤ d2) (hjoin : 1-a3 ≤ b)
    (hcap : (1-a3+r*(a3+1/2)+(3/2)*d)/(1+d) ≤ e2) : False := by
  let E : ℝ := (1-a3+r*(a3+1/2)+(3/2)*d)/(1+d)
  have hE : E ≤ e2 := hcap
  have hden : 0 < 1+d := by linarith
  have hEmul : E*(1+d)=1-a3+r*(a3+1/2)+(3/2)*d :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hnecessary : s+r*(1-a3)+E < 1+r := by
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · have hDz : D=1 := by rw [←hr0] at hDsq; nlinarith
      simp only [←hr0,zero_mul,add_zero]
      linarith only [hDz,hE,hmargins,hd2]
    · have hDu : D < 1+r := by nlinarith
      have hjoinmul := mul_le_mul_of_nonneg_left hjoin hr
      nlinarith only [hDu,hjoinmul,hforward,hE,hmargins]
  have hmul := mul_lt_mul_of_pos_right hnecessary hden
  have hprod : 0 ≤ r*(1/2-a3*d) := by
    apply mul_nonneg hr
    have htimes := mul_le_mul_of_nonneg_left hd1.le ha3
    nlinarith only [htimes,ha31]
  have hlarge : s+(1/2+s)*d < a3 := by
    nlinarith only [hmul,hEmul,hprod]
  have hstrict := mul_pos (show 0 < s-a/2 by linarith) hden
  have hsmall := t3_short_reach_cap hd hd1 hS hsq hbudget hP1 hP2
  nlinarith only [hlarge,hstrict,hsmall]

#print axioms t3_short_reach_cap
#print axioms nonnegative_t2_impossible

end
end HexagonCover.E4InsideSeamAlgebra
