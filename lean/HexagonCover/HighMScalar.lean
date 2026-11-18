import HexagonCover.HighMChart

/-! Exact scalar inequalities for the q=21/100 residual construction.
These source-exposed inequalities are proved for h≤M without using M<9/10;
the stronger scope must not be attributed to the source's original theorem. -/
namespace HexagonCover.HighMScalar
noncomputable section
open HeavyDepth
local notation "h₀" => NICertificate.halfRoot

def q : ℝ := 21/100
def A : ℝ := 13/4+3*q^2/4-h₀*q
def B : ℝ := 5/2+h₀*q
def C (r : ℝ) : ℝ := 13/3+q^2-4*h₀*q/3+(10/3+4*h₀*q/3)*r+4*r^2/3
def L (r : ℝ) : ℝ := 10*h₀/3+q+8*h₀*r/3
def E (M r : ℝ) : ℝ := M^2*(A+B*r+r^2)-M*S r*(B+2*r)+r+r^2
def X (D r : ℝ) : ℝ := D^2*C r-D*S r*L r+r+r^2

theorem root_bounds : (433:ℝ)/500<h₀ ∧ h₀<13/15 ∧ h₀<7/8 := by
  have hp := ExtremeTriangle.halfRoot_pos
  have hs := ExtremeTriangle.halfRoot_sq
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem S_upper {r : ℝ} (hr : 0≤r) : S r≤1+r/2+3*r^2/8 := by
  have hs := S_sq r
  unfold CornerChart.Q at hs
  have h3 : 0≤r^3 := pow_nonneg hr 3
  have h4 : 0≤r^4 := pow_nonneg hr 4
  have ht : 0≤1+r/2+3*r^2/8 := by positivity
  nlinarith only [hs,h3,h4,ht,S_pos r]

theorem box_bounds {r : ℝ} (hr : 0<r) (hr1 : r<7/20) :
    4<C r ∧ 0<L r ∧ L r<35/8 ∧ 3<A ∧ 0<B ∧ B<11/4 ∧ S r<49/40 := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hh1 : h₀<1 := by linarith [root_bounds.2.2]
  have hhr := mul_pos hh hr
  have hhrU := mul_lt_mul root_bounds.2.2 hr1.le hr (by norm_num : (0:ℝ)≤7/8)
  have hs := S_sq r
  unfold CornerChart.Q at hs
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · unfold C q
    nlinarith [sq_nonneg r]
  · unfold L q
    positivity
  · unfold L q
    nlinarith only [root_bounds.2.2,hhrU]
  · unfold A q
    nlinarith only [hh1]
  · unfold B q
    positivity
  · unfold B q
    nlinarith only [hh1]
  · nlinarith [S_pos r]

theorem X_at_lower (M r : ℝ) : X (h₀*M) r=E M r := by
  have hh3 : h₀^3=(3/4:ℝ)*h₀ := by rw [pow_succ,ExtremeTriangle.halfRoot_sq]
  unfold X E C L A B
  ring_nf
  simp only [ExtremeTriangle.halfRoot_sq,hh3]
  ring

def c0 : ℝ := h₀*(A*h₀-B)
def c1 : ℝ := (23-3*q)/8+(3*q-13)*h₀/4
def c2 : ℝ := 7/4-9*q/32-31*h₀/16
def lowerE (r : ℝ) : ℝ := c0+c1*r+c2*r^2-(3*h₀/4)*r^3

theorem lowerE_identity (r : ℝ) :
    h₀^2*(A+B*r+r^2)-h₀*(1+r/2+3*r^2/8)*(B+2*r)+r+r^2=lowerE r := by
  have hh3 : h₀^3=(3/4:ℝ)*h₀ := by rw [pow_succ,ExtremeTriangle.halfRoot_sq]
  unfold lowerE c0 c1 c2 A B
  ring_nf
  simp only [ExtremeTriangle.halfRoot_sq,hh3]
  ring

theorem lowerE_positive {r : ℝ} (hr : 0<r) (hr1 : r<7/20) : 3/1000<lowerE r := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hab : A*h₀-B=(122923*h₀-106300)/40000 := by
    unfold A B q
    nlinarith only [ExtremeTriangle.halfRoot_sq]
  have hc0 : 3/1000<c0 := by
    unfold c0
    rw [hab]
    have hh0 : 4/5<h₀ := by linarith [root_bounds.1]
    have hval : 75659/20000000<(122923*h₀-106300)/40000 := by
      linarith [root_bounds.1]
    have hm := mul_lt_mul hh0 hval.le (by norm_num : (0:ℝ)<75659/20000000) hh.le
    nlinarith only [hm]
  have hc2 : 0<c2 := by unfold c2 q; linarith [root_bounds.2.1]
  have hc1 : 0<c1-(3*h₀/4)*(7/20)^2 := by
    unfold c1 q
    linarith [root_bounds.2.2]
  have hrsq : r^2<(7/20)^2 := by nlinarith
  have hrpow := mul_lt_mul_of_pos_left hrsq (show 0<3*h₀/4 by positivity)
  have hp : 0<c1-(3*h₀/4)*r^2 := by linarith
  have hm := mul_pos hp hr
  have hc2r := mul_nonneg hc2.le (sq_nonneg r)
  unfold lowerE
  nlinarith only [hc0,hm,hc2r]

theorem E_height_positive {r : ℝ} (hr : 0<r) (hr1 : r<7/20) : 3/1000<E h₀ r := by
  have hb := box_bounds hr hr1
  have hmul := mul_le_mul_of_nonneg_left (S_upper hr.le)
    (mul_nonneg ExtremeTriangle.halfRoot_pos.le (by linarith [hb.2.2.2.2.1] : 0≤B+2*r))
  have he := lowerE_identity r
  have hp := lowerE_positive hr hr1
  unfold E
  nlinarith only [hmul,he,hp]

theorem E_mono_height {M r : ℝ} (hM : h₀≤M) (hr : 0<r) (hr1 : r<7/20) :
    E h₀ r≤E M r := by
  have hb := box_bounds hr hr1
  have hh0 : 6/7<h₀ := by linarith [root_bounds.1]
  have hP : 3<A+B*r+r^2 := by nlinarith [mul_pos hb.2.2.2.2.1 hr,sq_nonneg r]
  have hsum : 12/7<M+h₀ := by linarith
  have hmul := mul_lt_mul hsum hP.le (by norm_num : (0:ℝ)<3) (by linarith : 0≤M+h₀)
  have hB : B+2*r<69/20 := by linarith [hb.2.2.2.2.2.1]
  have hSB := mul_lt_mul hb.2.2.2.2.2.2 hB.le (by linarith [hb.2.2.2.2.1] : 0<B+2*r)
    (by norm_num : (0:ℝ)≤49/40)
  have hder : 0<(M+h₀)*(A+B*r+r^2)-S r*(B+2*r) := by nlinarith only [hmul,hSB]
  have hdiff := mul_nonneg (sub_nonneg.mpr hM) hder.le
  unfold E
  nlinarith only [hdiff]

theorem X_positive {M D r : ℝ} (hM : h₀≤M) (hD : h₀*M<D)
    (hr : 0<r) (hr1 : r<7/20) : 3/1000<X D r := by
  have hb := box_bounds hr hr1
  have hMh : 3/4≤h₀*M := by
    have hm := mul_le_mul_of_nonneg_left hM ExtremeTriangle.halfRoot_pos.le
    nlinarith only [hm,ExtremeTriangle.halfRoot_sq]
  have hsum : 3/2<D+h₀*M := by linarith
  have hmul := mul_lt_mul hsum hb.1.le (by norm_num : (0:ℝ)<4) (by linarith : 0≤D+h₀*M)
  have hSL := mul_lt_mul hb.2.2.2.2.2.2 hb.2.2.1.le hb.2.1
    (by norm_num : (0:ℝ)≤49/40)
  have hder : 0<(D+h₀*M)*C r-S r*L r := by nlinarith only [hmul,hSL]
  have hdiff := mul_pos (sub_pos.mpr hD) hder
  have hm := E_mono_height hM hr hr1
  have hp := E_height_positive hr hr1
  have he := X_at_lower M r
  unfold X at he ⊢
  nlinarith only [hdiff,hm,hp,he]

def linearS (u v x : ℝ) : ℝ := (u+v*x)/S x

theorem hasDerivAt_linearS (u v x : ℝ) :
    HasDerivAt (linearS u v) ((v-u/2+(v/2-u)*x)/(S x)^3) x := by
  have hn := ((hasDerivAt_id x).const_mul v).const_add u
  have hf := hn.div (hasDerivAt_S x) (ne_of_gt (S_pos x))
  convert hf using 1
  · ext z; rfl
  · dsimp
    field_simp [ne_of_gt (S_pos x)]
    ring_nf
    simp only [S_sq]
    unfold CornerChart.Q
    ring

theorem linearS_mono {u v x y : ℝ} (hfirst : 0<2*v-u) (hsecond : 0≤v-2*u)
    (hx : 0≤x) (hxy : x≤y) : linearS u v x≤linearS u v y := by
  have hm : StrictMonoOn (linearS u v) (Set.Ici (0:ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun z _ => (hasDerivAt_linearS u v z).continuousAt.continuousWithinAt
    intro z hz
    rw [interior_Ici] at hz
    rw [(hasDerivAt_linearS u v z).deriv]
    apply div_pos _ (pow_pos (S_pos z) 3)
    have hp := mul_nonneg (by linarith : 0≤v/2-u) hz.le
    linarith
  exact hm.monotoneOn hx (hx.trans hxy) hxy

def G (M r : ℝ) : ℝ := 2*h₀*(M*r-(1-M))+q*((1+M)+(2-M)*r)
def K (M : ℝ) : ℝ := 2*h₀*(1-M)+q*(1+M)
def X4 (D M r : ℝ) : ℝ := D^2*(1+q^2)-D*(G M r/S r)-M*(1-M)

theorem G_rstar {M : ℝ} (hM : 4/5<M) (hM1 : M<1) :
    G M (rstar M)/S (rstar M)=K M := by
  rw [S_rstar hM hM1]
  apply (div_eq_iff (ne_of_gt (show 0<M+rstar M by linarith [(rstar_bounds hM hM1).1]))).mpr
  have hrid : rstar M*(2*M-1)=1-M^2 := div_mul_cancel₀ _ (by linarith)
  have he : G M (rstar M)-K M*(M+rstar M)=
      (2*h₀-q)*(rstar M*(2*M-1)-(1-M^2)) := by unfold G K; ring
  rw [hrid,sub_self,mul_zero] at he
  linarith

theorem G_upper {M r : ℝ} (hM : h₀≤M) (hM1 : M<1)
    (hr : 0≤r) (hrstar : r≤rstar M) : G M r/S r≤K M := by
  let u := -2*h₀*(1-M)+q*(1+M)
  let v := 2*h₀*M+q*(2-M)
  have hM0 : 0<M := by linarith [root_bounds.1]
  have hM4 : 4/5<M := by linarith [root_bounds.1]
  have hh := ExtremeTriangle.halfRoot_pos
  have hu : 0<2*v-u := by
    have hp := mul_pos hh (show 0<1+M by linarith)
    have hq : 0≤q*(1-M) := by unfold q; linarith
    dsimp [u,v]
    nlinarith only [hp,hq]
  have hv : 0≤v-2*u := by
    have hp := mul_le_mul_of_nonneg_left (show 1≤2-M by linarith) hh.le
    have hq : 3*q*M/2<63/200 := by unfold q; linarith
    dsimp [u,v]
    nlinarith only [hp,hq,root_bounds.1]
  have hm := linearS_mono hu hv hr hrstar
  have he (x : ℝ) : linearS u v x=G M x/S x := by unfold linearS G u v; ring
  rw [he,he,G_rstar hM4 hM1] at hm
  exact hm

theorem X4_positive {M D r : ℝ} (hM : h₀≤M) (hM1 : M<1)
    (hD : h₀*M<D) (hr : 0≤r) (hrstar : r≤rstar M) : 0<X4 D M r := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hM0 : 0<M := by linarith [root_bounds.1]
  have hMh : 3/4≤h₀*M := by
    have hm := mul_le_mul_of_nonneg_left hM hh.le
    nlinarith only [hm,ExtremeTriangle.halfRoot_sq]
  have hD0 : 0<D := by linarith
  have hKu : K M<1 := by
    unfold K q
    nlinarith only [hMh,hM1,root_bounds.2.2]
  have hder : 0<(D+h₀*M)*(1+q^2)-K M := by
    have hp := mul_nonneg (show 0≤D+h₀*M by linarith) (sq_nonneg q)
    nlinarith only [hp,hKu,hMh,hD]
  have hdiff := mul_pos (sub_pos.mpr hD) hder
  have hGL := G_upper hM hM1 hr hrstar
  have hGD := mul_le_mul_of_nonneg_left hGL hD0.le
  have hid : (h₀*M)^2*(1+q^2)-h₀*M*K M-M*(1-M)=M*(A*M-B) := by
    unfold K A B
    ring_nf
    rw [ExtremeTriangle.halfRoot_sq]
    ring
  have hbase : 0<A*h₀-B := by
    have he : A*h₀-B=(122923*h₀-106300)/40000 := by
      unfold A B q
      nlinarith only [ExtremeTriangle.halfRoot_sq]
    rw [he]
    linarith [root_bounds.1]
  have hA : 0<A := by unfold A q; linarith [root_bounds.2.2]
  have hAM := mul_le_mul_of_nonneg_left hM hA.le
  have hpos := mul_pos hM0 (show 0<A*M-B by linarith)
  unfold X4
  nlinarith only [hdiff,hGD,hid,hpos]

end
end HexagonCover.HighMScalar

#print axioms HexagonCover.HighMScalar.X_positive
#print axioms HexagonCover.HighMScalar.X4_positive
