import HexagonCover.CornerChart

/-! Source-exposed central disk/two-point support lower bound. The circle
chord proof checks the full continuum of normal directions, including the
transition where a disk support and a point support agree. -/
namespace HexagonCover.HighMCentral
noncomputable section
open TriangleFrame SupportGeometry CornerChart
local notation "h₀" => NICertificate.halfRoot

/-- A linear functional on the upper unit-circle arc is bounded below by
its endpoint values. The proof is algebraic and includes both endpoints. -/
theorem circle_chord {l u yl yu x y α β B : ℝ}
    (hlu : l < u) (hx : l ≤ x) (hx' : x ≤ u)
    (hyl : 0 ≤ yl) (hyu : 0 ≤ yu) (hy : 0 ≤ y) (hβ : 0 ≤ β)
    (hl : l^2+yl^2=1) (hu : u^2+yu^2=1) (hunit : x^2+y^2=1)
    (hleft : B ≤ α*l+β*yl) (hright : B ≤ α*u+β*yu) :
    B ≤ α*x+β*y := by
  have hxl : 0 ≤ x-l := sub_nonneg.mpr hx
  have hxu : 0 ≤ u-x := sub_nonneg.mpr hx'
  let L := (u-x)*yl+(x-l)*yu
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : ((u-l)*y)^2-L^2 =
      (x-l)*(u-x)*((u-l)^2+(yu-yl)^2) := by
    dsimp [L]
    linear_combination (u-l)^2*hunit-(u-x)*(u-l)*hl-(x-l)*(u-l)*hu
  have hs : L^2 ≤ ((u-l)*y)^2 := by
    have hn : 0 ≤ (x-l)*(u-x)*((u-l)^2+(yu-yl)^2) := by positivity
    linarith only [he,hn]
  have hchord : L ≤ (u-l)*y := (sq_le_sq₀ hL (mul_nonneg (sub_nonneg.mpr hlu.le) hy)).mp hs
  have hb := mul_le_mul_of_nonneg_left hchord hβ
  have hleft' := mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hx')
  have hright' := mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr hx)
  have hscaled : (u-l)*B ≤ (u-l)*(α*x+β*y) := by
    dsimp [L] at hb
    nlinarith only [hb,hleft',hright']
  exact (mul_le_mul_iff_of_pos_left (sub_pos.mpr hlu)).mp hscaled

theorem scalar_alternatives {c z q u v k : ℝ}
    (hc : 1/2 ≤ c) (hz : 0 ≤ z) (hunit : c^2+z^2=1)
    (hq : 0 ≤ q) (hu0 : 1/2 < u) (hu1 : u < 1) (hv : 0 ≤ v)
    (huv : u^2+v^2=1) (htouch : u+q*v=1)
    (hleft : 1+k ≤ (1/2+h₀*q)*(1/2)+(h₀+3*q/2)*h₀)
    (hright : 1+k ≤ (1/2+h₀*q)*u+(h₀+3*q/2)*v) :
    1 ≤ c+q*z ∨ 1+k ≤ c+q*z+(-c/2+h₀*z+q*(h₀*c+z/2)) := by
  have hhpos := ExtremeTriangle.halfRoot_pos
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg z]
  by_cases hcu : u ≤ c
  · left
    have hh := circle_chord (l:=u) (u:=1) (yl:=v) (yu:=0) (α:=1) (β:=q) (B:=1)
      hu1 hcu hc1 hv (by norm_num) hz hq huv (by norm_num) hunit
      (by linarith only [htouch]) (by norm_num)
    simpa using hh
  · right
    have hh := circle_chord (l:=1/2) (u:=u) (yl:=h₀) (yu:=v)
      (α:=1/2+h₀*q) (β:=h₀+3*q/2) (B:=1+k)
      hu0 hc (lt_of_not_ge hcu).le ExtremeTriangle.halfRoot_pos.le hv hz
      (by positivity) (by nlinarith [ExtremeTriangle.halfRoot_sq]) huv hunit hleft hright
    nlinarith only [hh]

theorem scalar_twenty {c z : ℝ} (hc : 1/2 ≤ c) (hz : 0 ≤ z) (hu : c^2+z^2=1) :
    1 ≤ c+z/5 ∨ 1+1/15 ≤ c+z/5+(-c/2+h₀*z+(h₀*c+z/2)/5) := by
  have hh : (173:ℝ)/200 < h₀ := by nlinarith [ExtremeTriangle.halfRoot_sq,ExtremeTriangle.halfRoot_pos]
  have hs := scalar_alternatives (q:=1/5) (u:=12/13) (v:=5/13) (k:=1/15)
    hc hz hu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by nlinarith [ExtremeTriangle.halfRoot_sq]) (by nlinarith)
  convert hs using 1 <;> ring_nf

theorem scalar_twentyone {c z : ℝ} (hc : 1/2 ≤ c) (hz : 0 ≤ z) (hu : c^2+z^2=1) :
    1 ≤ c+21*z/100 ∨ 1+9/100 ≤ c+21*z/100+(-c/2+h₀*z+21*(h₀*c+z/2)/100) := by
  have hh : (173:ℝ)/200 < h₀ := by nlinarith [ExtremeTriangle.halfRoot_sq,ExtremeTriangle.halfRoot_pos]
  have hs := scalar_alternatives (q:=21/100) (u:=9559/10441) (v:=4200/10441) (k:=9/100)
    hc hz hu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by nlinarith [ExtremeTriangle.halfRoot_sq]) (by nlinarith)
  convert hs using 1 <;> ring_nf

theorem reflected_involution (flip : Bool) (p : Plane) :
    maybeReflect flip (maybeReflect flip p)=p := by
  cases flip <;> simp [maybeReflect,reflect_reflect]

theorem reflected_norm (flip : Bool) (p : Plane) : ‖maybeReflect flip p‖=‖p‖ := by
  cases flip
  · rfl
  · simpa only [maybeReflect,ite_true,show reflect (0:Plane)=0 by ext i; fin_cases i <;> simp [reflect],dist_zero_right]
      using reflection_dist p 0

theorem offsets_of_ball (T : UnitTriangle) {R c z : ℝ} {offs : Fin 3 → ℝ} {flip : Bool}
    (hr : 0 ≤ R) (hu : c^2+z^2=1)
    (hball : Metric.closedBall (0:Plane) R ⊆ T.region)
    (hm : ∀p,p∈T.region ↔ ∀i,dotp (nvec c z i) (maybeReflect flip p) ≤ offs i)
    (i : Fin 3) : R ≤ offs i := by
  let p := maybeReflect flip (R • nvec c z i)
  have hp : p∈T.region := by
    apply hball
    simp only [p,Metric.mem_closedBall,dist_zero_right,reflected_norm,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg hr,ExteriorLoss.nvec_norm hu,mul_one,le_refl]
  have hi := (hm p).mp hp i
  dsimp [p] at hi
  rw [reflected_involution,dotp_smul_right,nvec_gram hu i i] at hi
  simpa using hi

theorem axis_bound (T : UnitTriangle) {D R q : ℝ} (hD : 0 < D) (hR : 0 ≤ R)
    (hball : Metric.closedBall (0:Plane) R ⊆ T.region)
    (hplus : point D (q*D)∈T.region) (hminus : point D (-q*D)∈T.region)
    (hcase : (q=1/5 ∧ R ≤ D/15) ∨ (q=21/100 ∧ R ≤ 9*D/100)) :
    D+2*R ≤ h₀ := by
  obtain ⟨flip,c,z,offs,hc,hz,hu,hsum,hm⟩ := exists_corner_frame T
  have hoff := offsets_of_ball T hR hu hball hm
  have hp : dotp (nvec c z 0) (point D (q*D)) ≤ offs 0 := by
    cases flip
    · exact (hm _).mp hplus 0
    · simpa [maybeReflect,reflect,nvec,NICertificate.normalValues,dotp,point] using (hm _).mp hminus 0
  have hn : dotp (nvec c z 2) (point D (-q*D)) ≤ offs 2 := by
    cases flip
    · exact (hm _).mp hminus 2
    · simpa [maybeReflect,reflect,nvec,NICertificate.normalValues,dotp,point] using (hm _).mp hplus 2
  change c*D+z*(q*D) ≤ offs 0 at hp
  have hn' : D*(-c/2+h₀*z+q*(h₀*c+z/2)) ≤ offs 2 := by
    calc
      _ = dotp (nvec c z 2) (point D (-q*D)) := by
        norm_num [nvec,NICertificate.normalValues,dotp,point]
        ring
      _ ≤ _ := hn
  rcases hcase with ⟨rfl,hrange⟩ | ⟨rfl,hrange⟩
  · rcases scalar_twenty hc hz hu with ha | hb
    · nlinarith [mul_le_mul_of_nonneg_left ha hD.le,hoff 1,hoff 2]
    · nlinarith [mul_le_mul_of_nonneg_left hb hD.le,hoff 1,hn']
  · rcases scalar_twentyone hc hz hu with ha | hb
    · nlinarith [mul_le_mul_of_nonneg_left ha hD.le,hoff 1,hoff 2]
    · nlinarith [mul_le_mul_of_nonneg_left hb hD.le,hoff 1,hn']

#print axioms axis_bound
end
end HexagonCover.HighMCentral
