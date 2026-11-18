import HexagonCover.HeavyReach

/-! Source-exposed finite depth of the same actual heavy triangle.
The full-triangle bound is W(M); the smaller 2h(1-M) is not asserted here. -/
namespace HexagonCover.HeavyDepth
noncomputable section
open TriangleFrame SupportGeometry ExteriorLoss CornerChart ClippedCornerArea
local notation "h₀" => NICertificate.halfRoot

def W (M : ℝ) : ℝ := h₀*(1-M^2)/(1-M+M^2)
def rstar (M : ℝ) : ℝ := (1-M^2)/(2*M-1)
def S (x : ℝ) : ℝ := Real.sqrt (Q x)
def F (M x : ℝ) : ℝ := ((1+x)*S x-M-x)/Q x

theorem S_pos (x : ℝ) : 0 < S x := Real.sqrt_pos.mpr (Q_pos x)
theorem S_sq (x : ℝ) : (S x)^2=Q x := Real.sq_sqrt (Q_pos x).le

theorem S_ge_one {x : ℝ} (hx : 0 ≤ x) : 1 ≤ S x := by
  have hs := S_sq x
  have hp := (S_pos x).le
  unfold Q at hs
  nlinarith [sq_nonneg x]

theorem hasDerivAt_Q (x : ℝ) : HasDerivAt Q (1+2*x) x := by
  convert (((hasDerivAt_id x).const_add 1).add ((hasDerivAt_id x).pow 2)) using 1
  · ext z
    simp [Q]
  · norm_num

theorem hasDerivAt_S (x : ℝ) : HasDerivAt S ((1+2*x)/(2*S x)) x := by
  exact (hasDerivAt_Q x).sqrt (ne_of_gt (Q_pos x))

theorem hasDerivAt_F (M x : ℝ) :
    HasDerivAt (F M) (((1-x)*S x/2+M-1+2*M*x+x^2)/(Q x)^2) x := by
  have hs := hasDerivAt_S x
  have hn := ((((hasDerivAt_id x).const_add 1).mul hs).sub_const M).sub (hasDerivAt_id x)
  have hf := hn.div (hasDerivAt_Q x) (ne_of_gt (Q_pos x))
  have hsq := S_sq x
  have hcube : (S x)^3=Q x*S x := by rw [pow_succ,hsq]
  convert hf using 1
  · funext z; rfl
  · dsimp
    field_simp [ne_of_gt (S_pos x),ne_of_gt (Q_pos x)]
    ring_nf
    simp only [hsq,hcube]
    unfold Q
    ring

theorem F_strictMono {M : ℝ} (hM : 4/5 < M) : StrictMonoOn (F M) (Set.Icc (0:ℝ) (3/5)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (3/5))
  · exact fun x _ => (hasDerivAt_F M x).continuousAt.continuousWithinAt
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_F M x).deriv]
  apply div_pos _ (sq_pos_of_pos (Q_pos x))
  rcases hx with ⟨hx0,hx1⟩
  have hMp : 0 < M := by linarith
  have hs := S_ge_one hx0.le
  have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ 1-x)
  have hMx : 0 ≤ 2*M*x := by positivity
  nlinarith [sq_nonneg x]

theorem rstar_bounds {M : ℝ} (hM : 4/5 < M) (hM1 : M < 1) :
    0 < rstar M ∧ rstar M < 3/5 := by
  have hden : 0 < 2*M-1 := by linarith
  have hnum : 0 < 1-M^2 := by nlinarith
  constructor
  · exact div_pos hnum hden
  · apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_nonneg (M-4/5)]

theorem S_rstar {M : ℝ} (hM : 4/5 < M) (hM1 : M < 1) : S (rstar M)=M+rstar M := by
  have hr := (rstar_bounds hM hM1).1
  have hden : 2*M-1≠0 := by linarith
  apply (sq_eq_sq₀ (S_pos _).le (by linarith)).mp
  rw [S_sq]
  have hrid : rstar M*(2*M-1)=1-M^2 := div_mul_cancel₀ _ hden
  unfold Q
  nlinarith only [hrid]

theorem F_rstar {M : ℝ} (hM : 4/5 < M) (hM1 : M < 1) : h₀*F M (rstar M)=W M := by
  have hS := S_rstar hM hM1
  have hden : 2*M-1≠0 := by linarith
  have hquad : 1-M+M^2≠0 := by nlinarith [sq_nonneg (M-1/2)]
  have hp : 0 < M+rstar M := by linarith [(rstar_bounds hM hM1).1]
  have hrid : rstar M*(2*M-1)=1-M^2 := div_mul_cancel₀ _ hden
  have heD : 1-M+M^2=(M+rstar M)*(2*M-1) := by nlinarith only [hrid]

  calc
    h₀*F M (rstar M) = h₀*rstar M/(M+rstar M) := by
      unfold F
      rw [hS,←S_sq,hS]
      field_simp [ne_of_gt hp]
      ring
    _ = W M := by
      unfold W
      apply (div_eq_div_iff (ne_of_gt hp) hquad).mpr
      rw [heD]
      calc
        _ = h₀*(rstar M*(2*M-1))*(M+rstar M) := by ring
        _ = _ := by rw [hrid]

/-- Scalar orientation envelope, with strictness only from a strict orientation bound. -/
theorem envelope_bound {M x : ℝ} (hM : 4/5 < M) (hM1 : M < 1)
    (hx : 0 ≤ x) (hxr : x ≤ rstar M) :
    h₀*F M x ≤ W M ∧ (x < rstar M → h₀*F M x < W M) := by
  have hr := rstar_bounds hM hM1
  have hxmem : x∈Set.Icc (0:ℝ) (3/5) := ⟨hx,hxr.trans hr.2.le⟩
  have hrmem : rstar M∈Set.Icc (0:ℝ) (3/5) := ⟨hr.1.le,hr.2.le⟩
  rw [←F_rstar hM hM1]
  exact ⟨mul_le_mul_of_nonneg_left ((F_strictMono hM).monotoneOn hxmem hrmem hxr)
    ExtremeTriangle.halfRoot_pos.le,
    fun hlt => mul_lt_mul_of_pos_left (F_strictMono hM hxmem hrmem hlt) ExtremeTriangle.halfRoot_pos⟩

def upperDepth (p : Plane) : ℝ := h₀*(1-p 0)-p 1/2
def lowerDepth (p : Plane) : ℝ := h₀*(1-p 0)+p 1/2

theorem c_mul_S {c x : ℝ} (hc : 0 < c) (hi : c^2*Q x=h₀^2) : c*S x=h₀ := by
  apply (sq_eq_sq₀ (mul_pos hc (S_pos x)).le ExtremeTriangle.halfRoot_pos.le).mp
  rw [mul_pow,S_sq,hi]

theorem support_upper_short {c x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 < x) (hx1 : x ≤ 1) (hi : c^2*Q x=h₀^2)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (h0 : c*(a*x) ≤ offs 0) (h1 : c*a ≤ offs 1) (h2 : c*b ≤ offs 2)
    (hab : 1 ≤ a+b) : a < 4/5 := by
  have hgap := mul_nonneg hc.le (show 0 ≤ a+b-1 by linarith)
  have hb : c*(1+a*x) ≤ h₀ := by nlinarith only [hsum,h0,h1,h2,hgap]
  have hS := c_mul_S hc hi
  have hb' : 1+a*x ≤ S x := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    nlinarith only [hb,hS]
  by_contra ha
  have ha' : 4/5 ≤ a := le_of_not_gt ha
  have hb'' : 1+(4/5)*x ≤ S x := by nlinarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 1+(4/5)*x) (S_pos x).le).mpr hb''
  rw [S_sq] at hsq
  unfold Q at hsq
  have hxx : x^2 ≤ x := by nlinarith
  nlinarith

theorem support_orientation {c x a M : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 < x) (hi : c^2*Q x=h₀^2)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (h0 : c*(a*x) ≤ offs 0) (h1M : c*(M*x) ≤ offs 1) (h2 : c*M ≤ offs 2)
    (hab : 1 ≤ a+M) (hM : 4/5 < M) : x ≤ rstar M := by
  have hgap := mul_nonneg (mul_pos hc hx).le (show 0 ≤ a+M-1 by linarith)
  have hb : c*(M+x) ≤ h₀ := by nlinarith only [hsum,h0,h1M,h2,hgap]
  have hS := c_mul_S hc hi
  have hb' : M+x ≤ S x := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    nlinarith only [hb,hS]
  have hm0 : 0 < M := by linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ M+x) (S_pos x).le).mpr hb'
  rw [S_sq] at hsq
  unfold Q at hsq
  apply (le_div_iff₀ (by linarith : 0 < 2*M-1)).mpr
  nlinarith only [hsq]

theorem support_depth_numerator {c x a M : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 < x)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (h0 : c*(a*x) ≤ offs 0) (h2 : c*M ≤ offs 2) (hab : 1 ≤ a+M) :
    x*offs 0+(1+x)*offs 1 ≤ (1+x)*h₀-c*(M+x) ∧
      (1 < a+M → x*offs 0+(1+x)*offs 1 < (1+x)*h₀-c*(M+x)) := by
  have h2' := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1+x)
  have hgap := mul_nonneg (mul_pos hc hx).le (show 0 ≤ a+M-1 by linarith)
  have hsum' := congrArg (fun z : ℝ => (1+x)*z) hsum
  constructor
  · nlinarith only [h0,h2',hgap,hsum']
  · intro hs
    have hg := mul_pos (mul_pos hc hx) (show 0 < a+M-1 by linarith)
    nlinarith only [h0,h2',hg,hsum']

theorem cone_reconstruct (p : Plane) : conePoint (plusForm p) (minusForm p)=p := by
  ext i
  fin_cases i <;> simp [conePoint,plusForm,minusForm,NICertificate.halfRoot]
  all_goals field_simp [StandardCover.sqrt3_ne_zero] <;> ring

theorem lowerDepth_cone (P N : ℝ) : lowerDepth (corner+conePoint P N) = -h₀*N := by
  simp [lowerDepth,corner,conePoint]
  ring

/-- The inward depth is a positive combination of two actual side inequalities.
This directly bounds every point of the finite triangle. -/
theorem actual_support_depth (T : UnitTriangle) {c d x : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 < x) (hparam : parameter c d=x)
    (hmem : ∀ z : Plane, corner+z∈T.region ↔ ∀ i,dotp (nvec c d i) z ≤ offs i)
    {p : Plane} (hp : p∈T.region) :
    lowerDepth p ≤ h₀/(c*Q x)*(x*offs 0+(1+x)*offs 1) := by
  let P := plusForm (p-corner)
  let N := minusForm (p-corner)
  have he : corner+conePoint P N=p := by rw [cone_reconstruct]; abel
  have hpoly := (hmem (conePoint P N)).mp (by rw [he]; exact hp)
  have h0 := hpoly 0
  have h1 := hpoly 1
  rw [chart_dot (ne_of_gt hc),hparam] at h0 h1
  norm_num at h0 h1
  have h0' := mul_le_mul_of_nonneg_left h0 hx.le
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1+x)
  have hb : -c*Q x*N ≤ x*offs 0+(1+x)*offs 1 := by
    unfold Q
    nlinarith only [h0',h1']
  have hmul := mul_le_mul_of_nonneg_left hb ExtremeTriangle.halfRoot_pos.le
  have hd : lowerDepth p = -h₀*N := by rw [←he,lowerDepth_cone]
  rw [hd,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hc (Q_pos x))).mpr
  nlinarith only [hmul]

theorem scalar_depth_identity {c x M : ℝ} (hc : 0 < c) (hi : c^2*Q x=h₀^2) :
    h₀/(c*Q x)*((1+x)*h₀-c*(M+x)) = h₀*F M x := by
  have he : c=h₀/S x := (eq_div_iff (ne_of_gt (S_pos x))).mpr (c_mul_S hc hi)
  rw [he]
  unfold F
  rw [←S_sq]
  field_simp [ne_of_gt (S_pos x),ne_of_gt ExtremeTriangle.halfRoot_pos]
  ring

/-- Conditional chart theorem: its hypotheses are supplied by actual_triangle_depth. -/
theorem charted_depth (T : UnitTriangle) {c d x a M : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 < x) (hi : c^2*Q x=h₀^2) (hparam : parameter c d=x)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (hmem : ∀ z : Plane, corner+z∈T.region ↔ ∀ i,dotp (nvec c d i) z ≤ offs i)
    (ha : upperEndpoint a∈T.region) (hMmem : lowerEndpoint M∈T.region)
    (hab : 1 ≤ a+M) (hM : 4/5 < M) (hM1 : M < 1) :
    ∀p∈T.region,lowerDepth p ≤ W M ∧ (1 < a+M → lowerDepth p < W M) := by
  obtain ⟨h0,h1,h2,h1M⟩ := endpoint_support_bounds T (ne_of_gt hc) hparam hmem ha hMmem
  have hxr := support_orientation hc hx hi hsum h0 h1M h2 hab hM
  have hF := (envelope_bound hM hM1 hx.le hxr).1
  have hnum := support_depth_numerator hc hx hsum h0 h2 hab
  have hfac : 0 < h₀/(c*Q x) := div_pos ExtremeTriangle.halfRoot_pos (mul_pos hc (Q_pos x))
  have hupper := mul_le_mul_of_nonneg_left hnum.1 hfac.le
  rw [scalar_depth_identity hc hi] at hupper
  intro p hp
  have hdepth := actual_support_depth T hc hx hparam hmem hp
  refine ⟨hdepth.trans (hupper.trans hF),?_⟩
  intro hsumgt
  have hstrict := mul_lt_mul_of_pos_left (hnum.2 hsumgt) hfac
  rw [scalar_depth_identity hc hi] at hstrict
  exact (hdepth.trans_lt hstrict).trans_le hF

theorem charted_positive_parameter (T : UnitTriangle) {c d a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1/2 ≤ c) (hd : 0 ≤ d) (hu : c^2+d^2=1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : 1 ≤ a+b)
    (hsum : offs 0+offs 1+offs 2=h₀) (hpos : 0 < offs 0)
    (hmem : ∀ z : Plane,corner+z∈T.region ↔ ∀i,dotp (nvec c d i) z ≤ offs i)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region) :
    0 < parameter c d := by
  have hcp : 0 < c := by linarith
  obtain ⟨h0,h1,h2,h1b⟩ := endpoint_support_bounds T (ne_of_gt hcp) rfl hmem ha hb
  have hfeas := chart_feasibility hcp hu rfl ha0 hb0 hsum hpos h0 h1 h2 h1b
  have hxr := parameter_bounds hc hd hu
  by_contra hn
  have hlt := negative_chart_sum_lt_one hxr.1 (le_of_not_gt hn) hfeas.1
  linarith

theorem frame_short_upper (T : UnitTriangle) {c d a b r : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1/2 ≤ c) (hd : 0 ≤ d) (hu : c^2+d^2=1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : 1 ≤ a+b)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (hmem : ∀p : Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p ≤ offs i)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region) : a < 4/5 := by
  have hcp : 0 < c := by linarith
  have hsum' : translatedSupport c d offs 0+translatedSupport c d offs 1+
      translatedSupport c d offs 2=h₀ := by
    simpa only [Fin.sum_univ_three] using translated_support_sum (c:=c) (d:=d) hsum
  have hpos := translated_support_pos T hu hmem hr hball 0
  have hm := translated_membership T hmem
  have hx := charted_positive_parameter T hc hd hu ha0 hb0 hab hsum' hpos hm ha hb
  have hxr := parameter_bounds hc hd hu
  obtain ⟨h0,h1,h2,_⟩ := endpoint_support_bounds T (ne_of_gt hcp) rfl hm ha hb
  have hi : c^2*Q (parameter c d)=h₀^2 := by
    rw [ExtremeTriangle.halfRoot_sq]
    exact parameter_identity hcp hu
  exact support_upper_short hcp hx hxr.2 hi hsum' h0 h1 h2 hab

theorem depth_from_frame (T : UnitTriangle) {c d a M r : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1/2 ≤ c) (hd : 0 ≤ d) (hu : c^2+d^2=1)
    (ha0 : 0 ≤ a) (hab : 1 ≤ a+M) (hM : 4/5 < M) (hM1 : M < 1)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (hmem : ∀p : Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p ≤ offs i)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint M∈T.region) :
    ∀p∈T.region,lowerDepth p ≤ W M ∧ (1 < a+M → lowerDepth p < W M) := by
  have hcp : 0 < c := by linarith
  have hsum' : translatedSupport c d offs 0+translatedSupport c d offs 1+
      translatedSupport c d offs 2=h₀ := by
    simpa only [Fin.sum_univ_three] using translated_support_sum (c:=c) (d:=d) hsum
  have hpos := translated_support_pos T hu hmem hr hball 0
  have hm := translated_membership T hmem
  have hx := charted_positive_parameter T hc hd hu ha0 (by linarith) hab hsum' hpos hm ha hb
  have hi : c^2*Q (parameter c d)=h₀^2 := by
    rw [ExtremeTriangle.halfRoot_sq]
    exact parameter_identity hcp hu
  exact charted_depth T hcp hx hi rfl hsum' hm ha hb hab hM hM1

/-- Whole finite-triangle depth from its long upper hexagon edge. The same actual
unit triangle contains the strict anchor and both endpoints. Strict depth needs
strict heaviness; equality is allowed for reach sum exactly one. -/
theorem actual_triangle_depth (T : UnitTriangle) {a M r : ℝ}
    (ha0 : 0 ≤ a) (hab : 1 ≤ a+M) (hM : 4/5 < M) (hM1 : M < 1)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (hlong : upperEndpoint M∈T.region) (hshort : lowerEndpoint a∈T.region) :
    ∀p∈T.region,upperDepth p ≤ W M ∧ (1 < a+M → upperDepth p < W M) := by
  obtain ⟨flip,c,d,offs,hc,hd,hu,hsum,hmem⟩ := exists_corner_frame T
  cases flip
  · have hsmall := frame_short_upper T hc hd hu (by linarith) ha0 (by linarith)
      hsum hmem hr hball hlong hshort
    linarith
  · have hmemR : ∀p : Plane,p∈(reflectedTriangle T).region ↔
        ∀i,dotp (nvec c d i) p ≤ offs i := by
      intro p
      rw [reflectedTriangle_mem_iff,hmem]
      simp only [maybeReflect,ite_true,reflect_reflect]
    have ha : upperEndpoint a∈(reflectedTriangle T).region := by
      rw [reflectedTriangle_region]
      exact ⟨lowerEndpoint a,hshort,reflection_lowerEndpoint a⟩
    have hb : lowerEndpoint M∈(reflectedTriangle T).region := by
      rw [reflectedTriangle_region]
      exact ⟨upperEndpoint M,hlong,reflection_upperEndpoint M⟩
    have hdepth := depth_from_frame (reflectedTriangle T) hc hd hu ha0 hab hM hM1
      hsum hmemR hr (reflectedTriangle_ball T hball) ha hb
    intro p hp
    have hpR : reflect p∈(reflectedTriangle T).region := by
      rw [reflectedTriangle_region]
      exact ⟨p,hp,rfl⟩
    have he : lowerDepth (reflect p)=upperDepth p := by
      dsimp [lowerDepth,upperDepth,reflect]
      ring
    simpa only [he] using hdepth (reflect p) hpR

theorem W_den_pos (M : ℝ) : 0 < 1-M+M^2 := by nlinarith [sq_nonneg (M-1/2)]

/-- The source's exact coarse depth comparison for the positive-gap branch. -/
theorem W_lt_nineteen {M : ℝ} (hM : 9/10 < M) : W M < 19*h₀/91 := by
  have hpoly : 0 < (10*M-9)*(11*M+8) := mul_pos (by linarith) (by linarith)
  have hm := mul_pos ExtremeTriangle.halfRoot_pos hpoly
  unfold W
  apply (div_lt_iff₀ (W_den_pos M)).mpr
  nlinarith only [hm]

/-- The sharper 23/25 long-reach cutoff used by the same-C gap forcing. -/
theorem W_lt_thirtytwo {M : ℝ} (hM : 23/25 < M) : W M < 32*h₀/193 := by
  have hpoly : 0 < (25*M-23)*(9*M+7) := mul_pos (by linarith) (by linarith)
  have hm := mul_pos ExtremeTriangle.halfRoot_pos hpoly
  unfold W
  apply (div_lt_iff₀ (W_den_pos M)).mpr
  nlinarith only [hm]

end
end HexagonCover.HeavyDepth
