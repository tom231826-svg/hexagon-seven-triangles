import HexagonCover.Geometry

/-! Source-exposed T4 contact arithmetic. The negative branch only needs the
newly proved same-C midpoint obstruction at v>=3a/4; this avoids the stronger
old 5a/6 estimate and its auxiliary k<2a argument. -/
namespace HexagonCover.E4T4Scalar
noncomputable section

theorem forward_cases {a p b r d e : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hp : 0 < p) (hp1 : p < 1/2)
    (hb : 0 < b) (hd : 0 < d)
    (hPa0 : a/2-r*(1-a) < p) (hPa2 : 1-a+r*(1-a/2) < e)
    (hgap : b < 1-a)
    (hactive : -(1+r)*b=p ∨ r*b=d ∨ b=e) :
    -1/2 < r ∧ ((r < 0 ∧ e=b) ∨ (0 < r ∧ d=r*b)) := by
  have ha0 : 0 < 1-a := by linarith
  have hr : -1/2 < r := by
    by_contra hn
    have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) ha0.le
    nlinarith only [hx,hPa0,hp1]
  have hfirst : -(1+r)*b < 0 := mul_neg_of_neg_of_pos (by linarith) hb
  refine ⟨hr,?_⟩
  rcases hactive with hx | hx | hx
  · linarith
  · right
    refine ⟨?_,hx.symm⟩
    by_contra hn
    have he := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hb.le
    linarith
  · left
    refine ⟨?_,hx.symm⟩
    have hcoef : 0 < 1-a/2 := by linarith
    by_contra hn
    have he := mul_nonneg (le_of_not_gt hn) hcoef.le
    linarith

theorem positive_bounds {a p b r e S : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hp : a/2 < p) (hb : 1/2 < b)
    (hr : 0 < r) (hS : 0 ≤ S) (hsq : S^2=1+r+r^2)
    (hsum : p+r*b+e=S) (hPa : 1-a+r*(1-a/2) < e) :
    p<a ∧ r<4/21 := by
  have hcap : S<1+r := (sq_lt_sq₀ hS (by linarith)).mp (by nlinarith only [hsq,hr])
  have hba : 0 < b-a/2 := by linarith
  have hsmall : p-a+r*(b-a/2)<0 := by nlinarith only [hcap,hsum,hPa]
  have hp' : p<a := by nlinarith only [hsmall,mul_pos hr hba]
  have hrprod : r*(1-a)<a := by
    nlinarith only [hsmall,hp,mul_pos hr (show 0<b-1/2 by linarith)]
  have hratio : r<4/21 := by
    nlinarith only [hrprod,ha1,mul_pos hr (show 0<4/25-a by linarith)]
  exact ⟨hp',hratio⟩

theorem positive_contact_bounds {a p b r e S v : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hp : a/2 < p) (hb : 1/2 < b)
    (hr : 0 < r) (hS : 0 ≤ S) (hsq : S^2=1+r+r^2)
    (hsum : p+r*b+e=S) (hPa : 1-a+r*(1-a/2) < e)
    (hv : (1+2*r)*v=1+r-e) : a/2 < p ∧ p<v ∧ v<a := by
  obtain ⟨hpa,hrr⟩ := positive_bounds ha ha1 hp hb hr hS hsq hsum hPa
  have hden : 0 < 1+2*r := by linarith
  have hcap0 : 0 ≤ 1+r/2+r^2/2 := by positivity
  have hcap : S<1+r/2+r^2/2 := by
    apply (sq_lt_sq₀ hS hcap0).mp
    have he : (1+r/2+r^2/2)^2-S^2=(r*(1+r))^2/4 := by rw [hsq]; ring
    nlinarith only [he,sq_pos_of_pos (mul_pos hr (show 0<1+r by linarith))]
  have hbracket : 0 < 1/2+b-2*p-r/2 := by linarith
  have hpv : (1+2*r)*p < (1+2*r)*v := by
    nlinarith only [hv,hsum,hcap,mul_pos hr hbracket]
  have hva : (1+2*r)*v < (1+2*r)*a := by
    nlinarith only [hv,hPa,mul_pos ha hr]
  exact ⟨hp,(mul_lt_mul_iff_of_pos_left hden).mp hpv,
    (mul_lt_mul_iff_of_pos_left hden).mp hva⟩

theorem negative_contact_bounds {a p b k S v : ℝ}
    (ha : 0 < a) (ha1 : a < 4/25) (hk : 0 < k) (hk1 : k < 1/2)
    (hb : 0 < b) (hgap : b < 1-a)
    (hp : a/2+k*(1-a) < p) (hsum : p+b<S)
    (hS : 0 ≤ S) (hsq : S^2=1-k+k^2)
    (hv : (2-k)*v=2-k-2*b) : 3*a/4 < v ∧ v < 1 := by
  have hden : 0 < 2-k := by linarith
  have hcap0 : 0 ≤ 1-k/2+k^2/2 := by nlinarith [sq_nonneg k]
  have hcap : S<1-k/2+k^2/2 := by
    apply (sq_lt_sq₀ hS hcap0).mp
    have he : (1-k/2+k^2/2)^2-S^2=(k*(1-k))^2/4 := by rw [hsq]; ring
    nlinarith only [he,sq_pos_of_pos (mul_pos hk (show 0<1-k by linarith))]
  have hlower : (2-k)*(3*a/4)<(2-k)*v := by
    by_cases hka : k ≤ a/2
    · nlinarith only [hv,hgap,hka,mul_pos ha hk]
    · have hka' : a/2<k := lt_of_not_ge hka
      have hcoef : 0<1-5*a/4-k := by linarith
      nlinarith only [hv,hp,hsum,hcap,hka',mul_pos hk hcoef]
  have hupper : (2-k)*v < (2-k)*1 := by nlinarith only [hv,hb]
  exact ⟨(mul_lt_mul_iff_of_pos_left hden).mp hlower,
    (mul_lt_mul_iff_of_pos_left hden).mp hupper⟩

#print axioms forward_cases
#print axioms positive_contact_bounds
#print axioms negative_contact_bounds
end
end HexagonCover.E4T4Scalar
