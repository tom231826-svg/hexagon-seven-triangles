import HexagonCover.Geometry

/-! Scalar closure of the actual T1/T2 seam obligations. The large-s case
uses a monotone quadratic lower bound directly, so no derivative or separately
optimized triangle is introduced. These are explicitly conditional scalar
lemmas until ActualSeam supplies every input from one configuration. -/
namespace HexagonCover.E4InsideSeamScalar
noncomputable section

theorem nonnegative_chord {r D : ℝ} (hr : 0 ≤ r) (hD : 0<D)
    (hsq : D^2=1+r+r^2) : D ≤ 1+r := by
  nlinarith

theorem negative_scale {k D : ℝ} (hk : 0<k) (hk1 : k<1/2)
    (hD : 0<D) (hsq : D^2=1-k+k^2) :
    D<1 ∧ k*(1-k)/2<1-D ∧ k-2*(1-D)<k^2 := by
  have hD1 : D<1 := by nlinarith [mul_pos hk (show 0<1-k by linarith)]
  have hR : 0<1-D := by linarith
  have hrat : (1-D)*(1+D)=k*(1-k) := by nlinarith only [hsq]
  have hhalf : k*(1-k)/2<1-D := by
    nlinarith [mul_pos hR (show 0<1-D by linarith)]
  have hc : 0<1-k/2+k^2/2 := by nlinarith [sq_nonneg k]
  have hdiff : D^2<(1-k/2+k^2/2)^2 := by
    have hh := mul_pos (sq_pos_of_pos hk) (sq_pos_of_pos (show 0<1-k by linarith))
    nlinarith only [hsq,hh]
  have hchord : D<1-k/2+k^2/2 := (sq_lt_sq₀ hD.le hc.le).mp hdiff
  exact ⟨hD1,hhalf,by linarith⟩

theorem heavy_separation {t a : ℝ} (ht : 0<t) (ht1 : t<2/25)
    (ha : a<2*t) (hsq : a^2+a*(1-t)+(1-t)^2 ≤ 1) : 2*t-a>2*t^2 := by
  have hd : 0<2*t-a := by linarith
  have hquad : 3*t^2-(1+3*t)*(2*t-a)+(2*t-a)^2 ≤ 0 := by nlinarith only [hsq]
  by_contra hn
  have hle : 2*t-a ≤ 2*t^2 := le_of_not_gt hn
  have hp := mul_nonneg (show 0 ≤ 1+3*t by linarith) (sub_nonneg.mpr hle)
  have hq := mul_pos (sq_pos_of_pos ht) (show 0<1-6*t by linarith)
  nlinarith [sq_nonneg (2*t-a)]

/-- La alone suffices for nonnegative r; no cap point or r<1 is needed. -/
theorem nonnegative_lower_impossible {r D s a a3 b d e : ℝ}
    (hr : 0 ≤ r) (hD : 0<D) (hsq : D^2=1+r+r^2)
    (hs : a/2<s) (ha : 0<a) (ha3 : a3<1/3)
    (hb : 1-a3 ≤ b) (hd : r*b ≤ d)
    (he : 1-a/2+r*(1+a)/2 ≤ e) (hsum : s+d+e=D) : False := by
  have hc := nonnegative_chord hr hD hsq
  have hp := mul_nonneg hr (sub_nonneg.mpr hb)
  have hq := mul_nonneg hr (show 0 ≤ 1/2-a3+a/2 by linarith)
  nlinarith

theorem nonnegative_upper_impossible {r D a1 s t b d e : ℝ}
    (hr : 0 ≤ r) (hD : 0<D) (hsq : D^2=1+r+r^2)
    (ht : 0<t) (ht1 : t<2/25) (hs : s<23/100)
    (ha1 : t ≤ a1) (hb : 1-s ≤ b) (hd : r*b ≤ d)
    (he : 1-2*t/3+r*(1-4*t/3) ≤ e) (hsum : a1+d+e=D) : False := by
  have hc := nonnegative_chord hr hD hsq
  have hp := mul_nonneg hr (sub_nonneg.mpr hb)
  have hq := mul_nonneg hr (show 0 ≤ 1-s-4*t/3 by linarith)
  nlinarith

theorem negative_upper_impossible {v D a1 s t b d : ℝ}
    (hv : 0<v) (hv1 : v<1/2) (hD : 0<D) (hsq : D^2=1-v+v^2)
    (ht : 0<t) (ht1 : t<2/25) (hs : s ≤ 6*t/5)
    (ha1 : t ≤ a1) (hb : 1-s ≤ b) (hd : 0<d)
    (he : 1-2*t/3-v*(1-4*t/3) ≤ b) (hsum : a1+d+b=D) : False := by
  obtain ⟨hD1,hR,hchord⟩ := negative_scale hv hv1 hD hsq
  have hRsmall : 1-D<t/5 := by linarith
  have hquarter : v/4<1-D := by
    have hp := mul_pos hv (show 0<1/2-v by linarith)
    nlinarith
  have hvsmall : v<1/10 := by linarith
  have hnine : 9*v/20<1-D := by
    have hp := mul_pos hv (show 0<1/10-v by linarith)
    nlinarith
  have hvt := mul_pos hv ht
  have hc : 1-D+t/3<v := by nlinarith
  linarith

theorem upper_slope {t s k : ℝ} (ht : 0<t) (ht1 : t<2/25)
    (hs : s ≤ 6*t/5) (hrow : 2*t/3+k*(1-4*t/3) ≤ s) : k<3*t/5 := by
  by_contra hn
  have hk : 3*t/5 ≤ k := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ 1-4*t/3 by linarith)
  have hq := mul_pos ht (show 0<1/15-4*t/5 by linarith)
  nlinarith

theorem small_lower_impossible {t s a k D : ℝ}
    (ht : 0<t) (ht1 : t<2/25) (hs : t ≤ s)
    (ha : 0<a) (hat : a<2*t) (hsep : 2*t-a>2*t^2)
    (hk : 0<k) (hk1 : k<1/2) (hkt : k<3*t/5)
    (hD : 0<D) (hsq : D^2=1-k+k^2)
    (hG : 2*s-a-a*k-k+2*(1-D)<0) : False := by
  have hb := (negative_scale hk hk1 hD hsq).2.2
  have hak := mul_pos hk (sub_pos.mpr hat)
  have hkt2 := mul_pos (sub_pos.mpr hkt) (show 0<k+3*t/5 by linarith)
  have htk := mul_pos ht (sub_pos.mpr hkt)
  nlinarith [sq_pos_of_pos ht]

/-- Polynomial lower envelope, monotone on the whole actual s window.
This avoids a separate calculus optimization of G(s,100s/81). -/
theorem large_lower_impossible {t s a k D : ℝ}
    (ht : 0<t) (ht1 : t<2/25) (hs0 : 6*t/5 ≤ s) (hs1 : s<23/100)
    (ha : 0<a) (hat : a<2*t) (hsep : 2*t-a>2*t^2)
    (hk : 0<k) (hk1 : k<1/2) (hks : k ≤ 100*s/81)
    (hD : 0<D) (hsq : D^2=1-k+k^2)
    (hG : 2*s-a-a*k-k+2*(1-D)<0) : False := by
  have hs : 0<s := by linarith
  have hb := (negative_scale hk hk1 hD hsq).2.2
  have hak := mul_nonneg ha.le (sub_nonneg.mpr hks)
  have hks2 := mul_nonneg (sub_nonneg.mpr hks) (show 0 ≤ 100*s/81+k by positivity)
  have hats := mul_pos hs (sub_pos.mpr hat)
  have hcoef : 0 ≤ 2-200*t/81-(10000/6561:ℝ)*(s+6*t/5) := by linarith
  have hmono := mul_nonneg (sub_nonneg.mpr hs0) hcoef
  have hmargin := mul_pos ht (show 0<2/5-(2302/729:ℝ)*t by linarith)
  nlinarith

#print axioms negative_upper_impossible
#print axioms large_lower_impossible

end
end HexagonCover.E4InsideSeamScalar
