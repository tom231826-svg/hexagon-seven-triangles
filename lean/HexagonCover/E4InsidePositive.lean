import HexagonCover.E4InsideCentral

/-! Source-exposed positive-T4 terminal support inequalities. These scalar
lemmas retain the entire central orientation interval [-1,1], including zero
and period endpoints. They are not yet an actual-cover exclusion: the raw
frame, contained disk and same-C residual contact must be derived geometrically.

The source's two concavity arguments are replaced by exact upper bounds for
sqrt(1+3c²), with explicit real-interval splits and no approximation tolerance. -/
namespace HexagonCover.E4InsidePositive
noncomputable section

theorem scale_bounds {c F : ℝ} (hF : 0 ≤ F) (hFsq : F^2=1+3*c^2) :
    1 ≤ F ∧ F ≤ 1+3*c^2/2 := by
  constructor
  · nlinarith [sq_nonneg c]
  · nlinarith [sq_nonneg (F-1)]

theorem scale_chord {c F : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hF : 0 ≤ F) (hFsq : F^2=1+3*c^2) : F ≤ 1+c := by
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]

/-- The two necessary positive-orientation support budgets are inconsistent.
Both endpoint c=0 and c=1 are retained. -/
theorem nonnegative_orientation_impossible {a δ c F : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hδ : a/4 < δ) (hδ1 : δ < 1/10)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hF : 0 ≤ F) (hFsq : F^2=1+3*c^2)
    (hP : 1+(1-2*a)*c+δ*F ≤ F)
    (hD : a+5/6+(21/10-a)*c+δ*F ≤ F) : False := by
  obtain ⟨hF1,hFu⟩ := scale_bounds hF hFsq
  have hδ0 : 0 < δ := by linarith
  have hδF : δ ≤ δ*F := by nlinarith [mul_nonneg hδ0.le (sub_nonneg.mpr hF1)]
  by_cases hsmall : c ≤ 1/5
  · have hfactor : 0 < 1-2*a-3*c/2 := by linarith
    have hprod := mul_nonneg hc hfactor.le
    nlinarith only [hP,hFu,hδF,hδ0,hprod]
  · have hcl : 1/5 ≤ c := le_of_lt (lt_of_not_ge hsmall)
    have hFc := scale_chord hc hc1 hF hFsq
    have hfactor : 0 < 11/10-a := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hcl) hfactor.le
    nlinarith only [hD,hFc,hδF,hprod,ha,hδ0]

/-- Negative orientations with k at least a/2 are also excluded. The proof
uses exact chord bounds on k≥1/3 and a quadratic bound on [a/2,1/3]. -/
theorem negative_large_impossible {a δ k F : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hδ : a/4 < δ) (hδ1 : δ < 1/10)
    (hk : a/2 ≤ k) (hk1 : k ≤ 1)
    (hF : 0 ≤ F) (hFsq : F^2=1+3*k^2)
    (hP : 1-a+(1+a)*k+2*δ*F ≤ F) : False := by
  have hk0 : 0 ≤ k := by linarith
  obtain ⟨hF1,hFu⟩ := scale_bounds hF hFsq
  have hδ0 : 0 < δ := by linarith
  by_cases hsmall : k ≤ 1/3
  · have hδF : a/2 < 2*δ*F := by
      have hmul := mul_nonneg hδ0.le (sub_nonneg.mpr hF1)
      nlinarith
    have hfactor : 0 ≤ 1+a/4-3*k/2 := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hk) hfactor
    nlinarith only [hP,hFu,hδF,hprod,sq_nonneg a]
  · have hkl : 1/3 ≤ k := le_of_lt (lt_of_not_ge hsmall)
    have hFc := scale_chord hk0 hk1 hF hFsq
    have hcoef : 0 ≤ 1-2*δ := by linarith
    have hupper := mul_le_mul_of_nonneg_left hFc hcoef
    have hδprod : 0 < (2*δ-a/2)*(1+k) := mul_pos (by linarith) (by linarith)
    have haprod := mul_nonneg ha.le (show 0 ≤ 3*k-1 by linarith)
    nlinarith only [hP,hupper,hδprod,haprod]

theorem small_negative_impossible {a δ k v F : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hδ : a/4 < δ)
    (hk : 0 < k) (hka : k < a/2) (hv : a/2 < v)
    (hF : 0 ≤ F) (hFsq : F^2=1+3*k^2)
    (hP : δ*F ≤ F-1+(1-2*a)*k)
    (hK : δ*F ≤ F-1+a-v-(1+a-3*v)*k) : False := by
  obtain ⟨hF1,hFu⟩ := scale_bounds hF hFsq
  have hδ0 : 0 < δ := by linarith
  have hδF : a/2 < 2*δ*F := by
    have hmul := mul_nonneg hδ0.le (sub_nonneg.mpr hF1)
    nlinarith
  have hfactor : 0 < 1-3*k := by linarith
  have hvprod := mul_pos (show 0 < v-a/2 by linarith) hfactor
  have hkprod := mul_pos hk (show 0 < a/2-k by linarith)
  nlinarith only [hP,hK,hFu,hδF,hvprod,hkprod]

/-- Raw three-side offsets of one common triangle cannot satisfy the disk,
P4, D and K duties. These are support tests for the same offsets and frame.
This theorem does not assert that an arbitrary actual C has this chart. -/
theorem support_budget_impossible {a δ c v F B T L : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hδ : a/4 < δ) (hδ1 : δ < 1/10)
    (hc0 : -1 ≤ c) (hc1 : c ≤ 1) (hv : a/2 < v)
    (hF : 0 ≤ F) (hFsq : F^2=1+3*c^2)
    (hsum : B+T+L=F)
    (hBdisk : δ*F ≤ B) (hTdisk : δ*F ≤ T) (hLdisk : δ*F ≤ L)
    (hBP : a+(2-a)*c ≤ B) (hTP : 1-a-(1+a)*c ≤ T)
    (hTD : 5/6+c/10 ≤ T) (hBK : v*(1+3*c) ≤ B) : False := by
  by_cases hc : 0 ≤ c
  · exact nonnegative_orientation_impossible ha ha1 hδ hδ1 hc hc1 hF hFsq
      (by linarith) (by linarith)
  · have hk : 0 < -c := by linarith
    have hksq : F^2=1+3*(-c)^2 := by nlinarith only [hFsq]
    by_cases hka : a/2 ≤ -c
    · exact negative_large_impossible ha ha1 hδ hδ1 hka (by linarith) hF hksq
        (by nlinarith only [hTP,hBdisk,hLdisk,hsum])
    · exact small_negative_impossible ha ha1 hδ hk (lt_of_not_ge hka) hv hF hksq
        (by nlinarith only [hBP,hTP,hLdisk,hsum])
        (by nlinarith only [hBK,hTP,hLdisk,hsum])

#print axioms support_budget_impossible

end
end HexagonCover.E4InsidePositive
