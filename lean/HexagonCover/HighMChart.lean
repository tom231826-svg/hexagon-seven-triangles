import HexagonCover.HeavyDepthTransport
import HexagonCover.HighMResidual

/-! Source-exposed extraction of the actual heavy supporting line. The
normal and line belong to the original triangle; a reflected coordinate frame
is used only internally, with every point transported back. -/
namespace HexagonCover.HighMChart
noncomputable section
open TriangleFrame SupportGeometry ExteriorLoss CornerChart ClippedCornerArea HeavyDepth
local notation "h₀" => NICertificate.halfRoot

def inward (r : ℝ) : Plane := point (h₀ * (1 + r) / S r) ((1-r)/(2*S r))

theorem inward_unit (r : ℝ) : dotp (inward r) (inward r) = 1 := by
  have hs := S_sq r
  have hh := ExtremeTriangle.halfRoot_sq
  dsimp [inward, dotp]
  field_simp [ne_of_gt (S_pos r)]
  unfold Q at hs
  nlinarith only [hs, hh]

theorem inward_from_frame {c v r : ℝ} (hc : 0 < c)
    (hparam : parameter c v = r) (hS : c*S r = h₀) :
    inward r = reflect (-nvec c v 1) := by
  have hcr : c*r = -c/2+h₀*v := by
    unfold parameter at hparam
    have hh := (div_eq_iff (ne_of_gt hc)).mp (show h₀*v/c=r+1/2 by linarith)
    nlinarith only [hh]
  have hSv : S r*v=r+1/2 := by
    have he : h₀*(r+1/2)=h₀*(S r*v) := by
      calc
        h₀*(r+1/2) = c*S r*(r+1/2) := by rw [hS]
        _ = (c*r+c/2)*S r := by ring
        _ = h₀*v*S r := by rw [show c*r+c/2=h₀*v by linarith only [hcr]]
        _ = h₀*(S r*v) := by ring
    exact (mul_left_cancel₀ (ne_of_gt ExtremeTriangle.halfRoot_pos) he).symm
  ext i
  fin_cases i
  · change h₀*(1+r)/S r = -(-1/2*c-h₀*v)
    apply (div_eq_iff (ne_of_gt (S_pos r))).mpr
    calc
      h₀*(1+r) = h₀/2+h₀*(r+1/2) := by ring
      _ = c*S r/2+h₀*(S r*v) := by rw [hS,hSv]
      _ = _ := by ring
  · change (1-r)/(2*S r) = -(-(h₀*c+-1/2*v))
    apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num) (S_pos r)))).mpr
    symm
    calc
      -(-(h₀*c+-1/2*v))*(2*S r) = 2*h₀*(c*S r)-S r*v := by ring
      _ = 2*h₀*h₀-(r+1/2) := by rw [hS,hSv]
      _ = 1-r := by nlinarith only [ExtremeTriangle.halfRoot_sq]

/-- Data extracted from one actual heavy triangle. No replacement pose is
introduced. `D` is its true supporting-line offset. -/
structure Witness (T : UnitTriangle) (M a : ℝ) where
  r : ℝ
  D : ℝ
  r_pos : 0 < r
  r_lt : r < rstar M
  lower : h₀*M < D
  upper : D ≤ h₀*(1+r*(1-M))/S r
  short : a ≤ 1+r-D*S r/h₀
  unit : dotp (inward r) (inward r) = 1
  halfplane : ∀ p ∈ T.region, D ≤ dotp (inward r) p

theorem from_reflected_frame (T : UnitTriangle) {c v a M ε : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1/2 ≤ c) (hv : 0 ≤ v) (hu : c^2+v^2=1)
    (ha0 : 0 ≤ a) (hab : 1 < a+M) (hM : 4/5 < M)
    (hsum : offs 0+offs 1+offs 2=h₀)
    (hmem : ∀ p : Plane, p∈T.region ↔ ∀ i,dotp (nvec c v i) (reflect p) ≤ offs i)
    (hε : 0 < ε) (hball : Metric.ball corner ε ⊆ T.region)
    (hlong : upperEndpoint M∈T.region) (hshort : lowerEndpoint a∈T.region) :
    Nonempty (Witness T M a) := by
  let r := parameter c v
  let s := translatedSupport c v offs
  let D := c*(1+r)-s 1
  have hcp : 0 < c := by linarith
  have hmR : ∀p : Plane,p∈(reflectedTriangle T).region ↔
      ∀i,dotp (nvec c v i) p ≤ offs i := by
    intro p
    rw [reflectedTriangle_mem_iff,hmem,reflect_reflect]
  have hshortR : upperEndpoint a∈(reflectedTriangle T).region := by
    rw [reflectedTriangle_region]
    exact ⟨lowerEndpoint a,hshort,reflection_lowerEndpoint a⟩
  have hlongR : lowerEndpoint M∈(reflectedTriangle T).region := by
    rw [reflectedTriangle_region]
    exact ⟨upperEndpoint M,hlong,reflection_upperEndpoint M⟩
  have hs : s 0+s 1+s 2=h₀ := by
    simpa only [Fin.sum_univ_three] using translated_support_sum (c:=c) (d:=v) hsum
  have hpos := translated_support_pos (reflectedTriangle T) hu hmR hε
    (reflectedTriangle_ball T hball) 0
  have hm := translated_membership (reflectedTriangle T) hmR
  have hr : 0 < r := charted_positive_parameter (reflectedTriangle T) hc hv hu
    ha0 (by linarith) hab.le hs hpos hm hshortR hlongR
  have hi : c^2*Q r=h₀^2 := by
    rw [ExtremeTriangle.halfRoot_sq]
    exact parameter_identity hcp hu
  have hS := c_mul_S hcp hi
  have hcrange := parameter_bounds hc hv hu
  obtain ⟨h0,h1,h2,h1M⟩ := endpoint_support_bounds (reflectedTriangle T)
    (ne_of_gt hcp) (show parameter c v=r from rfl) hm hshortR hlongR
  change c*(a*r) ≤ s 0 at h0
  change c*a ≤ s 1 at h1
  change c*M ≤ s 2 at h2
  change c*(M*r) ≤ s 1 at h1M
  have hgap := mul_pos (mul_pos hcp hr) (show 0 < a+M-1 by linarith)
  have hlt : c*(M+r)<h₀ := by nlinarith only [h0,h1M,h2,hs,hgap]
  have hMS : M+r<S r := by
    apply (mul_lt_mul_iff_of_pos_left hcp).mp
    nlinarith only [hlt,hS]
  have hsq : (M+r)^2 < (S r)^2 :=
    (sq_lt_sq₀ (by linarith : 0 ≤ M+r) (S_pos r).le).mpr hMS
  rw [S_sq] at hsq
  have hrstar : r<rstar M := by
    apply (lt_div_iff₀ (by linarith : 0 < 2*M-1)).mpr
    unfold Q at hsq
    nlinarith only [hsq]
  have hsep := (HeavyReach.support_separation hcp hr hcrange.2 hi hs h0 h1 h2 h1M hab.le).2 hab
  have hlower : h₀*M<D :=
    (mul_le_mul_of_nonneg_left (le_max_right a M) ExtremeTriangle.halfRoot_pos.le).trans_lt hsep
  have hcform : c=h₀/S r := (eq_div_iff (ne_of_gt (S_pos r))).mpr hS
  have hupper : D ≤ h₀*(1+r*(1-M))/S r := by
    have hbound : D≤c*(1+r*(1-M)) := by dsimp [D]; nlinarith only [h1M]
    calc
      D ≤ c*(1+r*(1-M)) := hbound
      _ = _ := by rw [hcform]; ring
  have hshortbound : a≤1+r-D*S r/h₀ := by
    have hbound : D≤c*(1+r-a) := by dsimp [D]; linarith only [h1]
    have hm := mul_le_mul_of_nonneg_right hbound (S_pos r).le
    have he : c*(1+r-a)*S r=h₀*(1+r-a) := by rw [mul_right_comm c _ (S r),hS]
    rw [he] at hm
    have hh : D*S r/h₀≤1+r-a :=
      (div_le_iff₀ ExtremeTriangle.halfRoot_pos).mpr (by nlinarith only [hm])
    linarith only [hh]
  have hD : D = -offs 1 := by
    dsimp [D,s,translatedSupport]
    rw [HeavyReach.corner_projection (ne_of_gt hcp) (show parameter c v=r from rfl)]
    ring
  refine ⟨⟨r,D,hr,hrstar,hlower,hupper,hshortbound,inward_unit r,?_⟩⟩
  intro p hp
  have hb := (hmem p).mp hp 1
  rw [inward_from_frame hcp (show parameter c v=r from rfl) hS]
  have he : dotp (reflect (-nvec c v 1)) p = -dotp (nvec c v 1) (reflect p) := by
    simp [dotp,reflect]
    ring
  rw [he,hD]
  linarith only [hb]

theorem actual_triangle (T : UnitTriangle) {a M ε : ℝ}
    (ha0 : 0 ≤ a) (hab : 1<a+M) (hM : 4/5<M)
    (hε : 0<ε) (hball : Metric.ball corner ε ⊆ T.region)
    (hlong : upperEndpoint M∈T.region) (hshort : lowerEndpoint a∈T.region) :
    Nonempty (Witness T M a) := by
  obtain ⟨flip,c,v,offs,hc,hv,hu,hsum,hmem⟩ := exists_corner_frame T
  cases flip
  · have hsmall := frame_short_upper T hc hv hu (by linarith) ha0
      (by linarith) hsum hmem hε hball hlong hshort
    linarith
  · exact from_reflected_frame T hc hv hu ha0 hab hM hsum hmem hε hball hlong hshort

/-- The witness refers to the same rotated heavy5 as all source-coordinate
endpoint and central-disk statements. -/
theorem actual_normalized {config : Fin 7 → UnitTriangle}
    (h : NormalizedHeavy.Normalized config) (hM : 4/5<NormalizedHeavy.M h) :
    Nonempty (Witness (SourceCoordinates.rotateConfig config 5)
      (NormalizedHeavy.M h) (Configuration.a h.cover 5)) := by
  obtain ⟨ε,hε,hball⟩ := HeavyDepthTransport.anchor_ball h
  obtain ⟨hlong,hshort⟩ := HeavyDepthTransport.actual_endpoints h
  exact actual_triangle _ (Configuration.leftReach h.cover 5).positive.le
    (NormalizedHeavy.structure_bounds h).2.2.1 hM hε hball hlong hshort

theorem Witness.lt_height {T : UnitTriangle} {M a : ℝ} (w : Witness T M a)
    (hM : 1/2<M) (hM1 : M<1) : w.D<h₀ := by
  have hs := S_sq w.r
  unfold Q at hs
  have hp := mul_pos (show 0<2*M-1 by linarith) w.r_pos
  have hq := mul_nonneg (mul_nonneg (by linarith : 0≤M) (by linarith : 0≤2-M))
    (sq_nonneg w.r)
  have hsf : 1+w.r*(1-M)<S w.r := by
    have hn : 0≤1+w.r*(1-M) := by
      have hh := mul_nonneg w.r_pos.le (by linarith : 0≤1-M)
      linarith
    nlinarith only [hs,hp,hq,hn,S_pos w.r]
  apply w.upper.trans_lt
  apply (div_lt_iff₀ (S_pos w.r)).mpr
  exact mul_lt_mul_of_pos_left hsf ExtremeTriangle.halfRoot_pos

theorem inward_bounds {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    h₀<(inward r) 0 ∧ (inward r) 0<1 ∧
      0<(inward r) 1 ∧ (inward r) 1<1/2 := by
  have hs := S_sq r
  have hs0 := S_pos r
  have hs1 := S_ge_one hr.le
  unfold Q at hs
  have hSl : S r<1+r := by nlinarith
  have hnx : h₀<(inward r) 0 := by
    change h₀<h₀*(1+r)/S r
    apply (lt_div_iff₀ hs0).mpr
    exact mul_lt_mul_of_pos_left hSl ExtremeTriangle.halfRoot_pos
  have hny : 0<(inward r) 1 :=
    div_pos (by linarith) (mul_pos (by norm_num) hs0)
  have hnyhalf : (inward r) 1<1/2 := by
    change (1-r)/(2*S r)<1/2
    apply (div_lt_iff₀ (mul_pos (by norm_num) hs0)).mpr
    linarith
  have hu := inward_unit r
  have hnx1 : (inward r) 0<1 := by
    unfold dotp at hu
    nlinarith [sq_pos_of_pos hny,ExtremeTriangle.halfRoot_pos]
  exact ⟨hnx,hnx1,hny,hnyhalf⟩

end
end HexagonCover.HighMChart

#print axioms HexagonCover.HighMChart.inward_unit
#print axioms HexagonCover.HighMChart.inward_from_frame
#print axioms HexagonCover.HighMChart.actual_normalized
#print axioms HexagonCover.HighMChart.Witness.lt_height
#print axioms HexagonCover.HighMChart.inward_bounds
