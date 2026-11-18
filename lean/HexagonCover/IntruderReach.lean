import HexagonCover.CommonReach

/-! Actual local H/D bounds and exact common-radius comparisons.
Source exposure is recorded in reach-geometry-exposure.md. -/
namespace HexagonCover.IntruderReach
noncomputable section
open TriangleFrame SupportGeometry ExteriorLoss CornerChart ClippedCornerArea HeavyReach

def q : ℝ := 1 / Real.sqrt 3

theorem halfRoot_q : NICertificate.halfRoot*q=1/2 := by
  unfold NICertificate.halfRoot q
  have hh : Real.sqrt (3:ℝ)≠0 := by positivity
  field_simp

theorem support_strict_half {c x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0<c) (hx : 0<x) (hx1 : x≤1)
    (hidentity : c^2*Q x=NICertificate.halfRoot^2)
    (hsum : offs 0+offs 1+offs 2=NICertificate.halfRoot)
    (h0 : c*(a*x)≤offs 0) (h1 : c*a≤offs 1) (h2 : c*b≤offs 2)
    (hab : 1≤a+b) : NICertificate.halfRoot/2<c*(1+x)-offs 1 := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hcx := mul_pos hc hx
  have hgap : c*(1+x/2)<NICertificate.halfRoot := by
    apply (sq_lt_sq₀ (by positivity : 0≤c*(1+x/2)) hh.le).mp
    unfold Q at hidentity
    nlinarith only [hidentity,sq_pos_of_pos hcx]
  have hoff : offs 0≤NICertificate.halfRoot-c := by
    nlinarith only [hsum,h1,h2,mul_nonneg hc.le (sub_nonneg.mpr hab)]
  have h02 : c*x≤offs 0+x*offs 2 := by
    nlinarith only [h0,mul_le_mul_of_nonneg_left h2 hx.le,
      mul_nonneg hcx.le (sub_nonneg.mpr hab)]
  have hbd : c*Q x-NICertificate.halfRoot≤x*(c*(1+x)-offs 1) := by
    have hm := mul_le_mul_of_nonneg_left hoff (sub_nonneg.mpr hx1)
    have hs := congrArg (fun z : ℝ => x*z) hsum
    unfold Q
    nlinarith only [hm,h02,hs]
  have hbd' : NICertificate.halfRoot*(NICertificate.halfRoot-c)≤
      c*x*(c*(1+x)-offs 1) := by
    have hm := mul_le_mul_of_nonneg_left hbd hc.le
    nlinarith only [hm,hidentity]
  have hgap' := mul_lt_mul_of_pos_left hgap hh
  apply (mul_lt_mul_iff_of_pos_left hcx).mp
  nlinarith only [hbd',hgap']

theorem charted_strict_separation (T : UnitTriangle) {c d a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1/2≤c) (hd : 0≤d) (hu : c^2+d^2=1)
    (ha0 : 0≤a) (hb0 : 0≤b) (hab : 1≤a+b)
    (hsum : offs 0+offs 1+offs 2=NICertificate.halfRoot) (hpos : ∀i,0<offs i)
    (hmem : ∀z : Plane,corner+z∈T.region ↔ ∀i,dotp (nvec c d i) z≤offs i)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region) :
    ∃D:ℝ,NICertificate.halfRoot/2<D ∧ ∀p∈T.region,D≤‖p‖ := by
  let x := parameter c d
  have hcpos : 0<c := by linarith
  have hparam : parameter c d=x := rfl
  have hxr := parameter_bounds hc hd hu
  obtain ⟨h0,h1,h2,h1b⟩ := endpoint_support_bounds T (ne_of_gt hcpos) hparam hmem ha hb
  have hfeas := chart_feasibility hcpos hu hparam ha0 hb0 hsum (hpos 0) h0 h1 h2 h1b
  have hx : 0<x := by
    by_contra hn
    have hh := negative_chart_sum_lt_one hxr.1 (le_of_not_gt hn) hfeas.1
    linarith
  have hi : c^2*Q x=NICertificate.halfRoot^2 := by
    rw [ExtremeTriangle.halfRoot_sq]; exact parameter_identity hcpos hu
  refine ⟨c*(1+x)-offs 1,support_strict_half hcpos hx hxr.2 hi hsum h0 h1 h2 hab,?_⟩
  intro p hp
  have hi := (hmem (p-corner)).mp (by simpa using hp) 1
  rw [dotp_sub_right,corner_projection (ne_of_gt hcpos) hparam] at hi
  have hn : ‖-nvec c d 1‖=1 := by rw [norm_neg,nvec_norm hu]
  have hdot := dotp_le_norm hn p
  have he : dotp (-nvec c d 1) p = -dotp (nvec c d 1) p := by simp [dotp]; ring
  rw [he] at hdot
  linarith

theorem strict_separation_from_frame (T : UnitTriangle) {c d a b r : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1/2≤c) (hd : 0≤d) (hu : c^2+d^2=1)
    (ha0 : 0≤a) (hb0 : 0≤b) (hab : 1≤a+b)
    (hsum : offs 0+offs 1+offs 2=NICertificate.halfRoot)
    (hmem : ∀p : Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p≤offs i)
    (hr : 0<r) (hball : Metric.ball corner r⊆T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region) :
    ∃D:ℝ,NICertificate.halfRoot/2<D ∧ ∀p∈T.region,D≤‖p‖ := by
  have hsum' : translatedSupport c d offs 0+translatedSupport c d offs 1+
      translatedSupport c d offs 2=NICertificate.halfRoot := by
    simpa only [Fin.sum_univ_three] using translated_support_sum (c:=c) (d:=d) hsum
  exact charted_strict_separation T hc hd hu ha0 hb0 hab hsum'
    (translated_support_pos T hu hmem hr hball) (translated_membership T hmem) ha hb

/-- D: a heavy actual triangle has a uniform separation strictly above h/2,
even at equality in the reach sum. -/
theorem actual_heavy_strict_half (T : UnitTriangle) {a b r : ℝ}
    (ha0 : 0≤a) (hb0 : 0≤b) (hab : 1≤a+b)
    (hr : 0<r) (hball : Metric.ball corner r⊆T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region) :
    ∃D:ℝ,NICertificate.halfRoot/2<D ∧ ∀p∈T.region,D≤‖p‖ := by
  obtain ⟨flip,c,d,offs,hc,hd,hu,hsum,hmem⟩ := exists_corner_frame T
  cases flip
  · exact strict_separation_from_frame T hc hd hu ha0 hb0 hab hsum hmem hr hball ha hb
  · have hmemR : ∀p : Plane,p∈(reflectedTriangle T).region ↔
        ∀i,dotp (nvec c d i) p≤offs i := by
      intro p; rw [reflectedTriangle_mem_iff,hmem]
      simp only [maybeReflect,ite_true,reflect_reflect]
    have hA : upperEndpoint b∈(reflectedTriangle T).region := by
      rw [reflectedTriangle_region]; exact ⟨lowerEndpoint b,hb,reflection_lowerEndpoint b⟩
    have hB : lowerEndpoint a∈(reflectedTriangle T).region := by
      rw [reflectedTriangle_region]; exact ⟨upperEndpoint a,ha,reflection_upperEndpoint a⟩
    obtain ⟨D,hD,hP⟩ := strict_separation_from_frame (reflectedTriangle T) hc hd hu
      hb0 ha0 (by linarith) hsum hmemR hr (reflectedTriangle_ball T hball) hA hB
    refine ⟨D,hD,?_⟩
    intro p hp
    have hm : reflect p∈(reflectedTriangle T).region := by
      rw [reflectedTriangle_region]; exact ⟨p,hp,rfl⟩
    simpa only [reflection_norm] using hP (reflect p) hm

/-- H: intruding and heavy force both actual reaches into the strict interval
(1-1/sqrt3,1/sqrt3), for the same triangle. -/
theorem actual_intruder_reaches (T : UnitTriangle) {a b r : ℝ}
    (ha0 : 0≤a) (hb0 : 0≤b) (hab : 1≤a+b)
    (hr : 0<r) (hball : Metric.ball corner r⊆T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region)
    (hin : ∃p∈T.region,‖p‖<1/2) :
    1-q<a ∧ a<q ∧ 1-q<b ∧ b<q := by
  obtain ⟨D,hD,_,hP⟩ := actual_heavy_reach_separation T ha0 hb0 hab hr hball ha hb
  obtain ⟨p,hp,hpn⟩ := hin
  have hm : max a b<q := by
    apply (mul_lt_mul_iff_of_pos_left ExtremeTriangle.halfRoot_pos).mp
    rw [halfRoot_q]
    exact lt_of_le_of_lt (hD.trans (hP p hp)) hpn
  have hqa := (le_max_left a b).trans_lt hm
  have hqb := (le_max_right a b).trans_lt hm
  exact ⟨by linarith,hqa,by linarith,hqb⟩

/-- Contrapositive of D in a form that can be used for a nearest outer owner. -/
theorem actual_close_is_light (T : UnitTriangle) {a b r : ℝ}
    (ha0 : 0≤a) (hb0 : 0≤b) (hr : 0<r) (hball : Metric.ball corner r⊆T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region)
    (hclose : ∃p∈T.region,‖p‖≤NICertificate.halfRoot/2) : a+b<1 := by
  by_contra h
  obtain ⟨D,hD,hP⟩ := actual_heavy_strict_half T ha0 hb0 (le_of_not_gt h) hr hball ha hb
  obtain ⟨p,hp,hpn⟩ := hclose
  linarith [hP p hp]

open CommonReach

def rmax (t : ℝ) : ℝ := (Real.sqrt 3-Real.sqrt (3-4*t+4*t^2))/4

theorem rho_gt_safe_radius {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    t*(1-t)/2<rho t := by
  let z := t*(1-t)
  have hz : 0<z := mul_pos ht (sub_pos.mpr ht1)
  have hz1 : z≤1/4 := by dsimp [z]; nlinarith [sq_nonneg (t-1/2)]
  have hsq : Real.sqrt (radiusSq t)^2=1-z := by
    rw [Real.sq_sqrt (radiusSq_pos t).le]; dsimp [radiusSq,z]; ring
  have hr0 := Real.sqrt_nonneg (radiusSq t)
  have hbound : Real.sqrt (radiusSq t)<1-z/2 := by
    apply (sq_lt_sq₀ hr0 (by linarith : 0≤1-z/2)).mp
    nlinarith [sq_pos_of_pos hz]
  dsimp [rho]
  change z/2<1-Real.sqrt (radiusSq t)
  linarith

theorem rmax_lt_safe_radius {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    rmax t<t*(1-t)/2 := by
  let z := t*(1-t)
  have hz : 0<z := mul_pos ht (sub_pos.mpr ht1)
  have hz1 : z≤1/4 := by dsimp [z]; nlinarith [sq_nonneg (t-1/2)]
  have hs3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hs30 := Real.sqrt_nonneg (3:ℝ)
  have hs31 : 3/2<Real.sqrt (3:ℝ) := by nlinarith
  have hrad : 0≤3-4*t+4*t^2 := by dsimp [z] at hz1; nlinarith
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (3-4*t+4*t^2)
  have hgap : 0<4*z*(Real.sqrt 3-1-z) := mul_pos (by positivity) (by linarith)
  have hgt : Real.sqrt 3-2*z<Real.sqrt (3-4*t+4*t^2) := by
    apply (sq_lt_sq₀ (by linarith : 0≤Real.sqrt 3-2*z) hs0).mp
    dsimp [z] at hgap ⊢
    nlinarith only [hgap,hs,hs3]
  unfold rmax
  change (Real.sqrt 3-Real.sqrt (3-4*t+4*t^2))/4<z/2
  linarith

theorem rho_gt_rmax {t : ℝ} (ht : 0<t) (ht1 : t<1) : rmax t<rho t :=
  (rmax_lt_safe_radius ht ht1).trans (rho_gt_safe_radius ht ht1)


/-- Monotonicity is confined to the increasing half of the edge parameter. -/
theorem rmax_mono {x y : ℝ} (hxy : x≤y) (hy : y≤1/2) : rmax x≤rmax y := by
  have hrad : 3-4*y+4*y^2≤3-4*x+4*x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0≤1-x-y by linarith)]
  have hs := Real.sqrt_le_sqrt hrad
  unfold rmax
  linarith

theorem rmax_half_lt_two_twentyfive : rmax (1/2)<2/25 := by
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hp2 := Real.sqrt_nonneg (2:ℝ)
  have hp3 := Real.sqrt_nonneg (3:ℝ)
  have hl : (561:ℝ)/400<Real.sqrt 2 := by nlinarith
  have hh : Real.sqrt 3<Real.sqrt 2+8/25 := by
    apply (sq_lt_sq₀ hp3 (by positivity)).mp
    nlinarith
  norm_num [rmax]
  linarith

theorem common_reach_feasible (T : UnitTriangle) {t : ℝ}
    (ha : upperEndpoint t∈T.region) (hb : lowerEndpoint t∈T.region) : 3*t^2≤1 := by
  have hd := T.dist_le_one ha hb
  have he : dist (upperEndpoint t) (lowerEndpoint t)^2=3*t^2 := by
    rw [dist_sq_coordinates]
    dsimp [upperEndpoint,lowerEndpoint,corner,upperRay,lowerRay]
    nlinarith only [congrArg (fun z : ℝ => 4*t^2*z) ExtremeTriangle.halfRoot_sq]
  nlinarith only [he,hd,dist_nonneg (x:=upperEndpoint t) (y:=lowerEndpoint t)]

/-- B-small, tied to a point of the same actual finite triangle. -/
theorem actual_common_reach_small (T : UnitTriangle) {t : ℝ} (ht : 0<t)
    (hu : corner∈T.region) (ha : upperEndpoint t∈T.region) (hb : lowerEndpoint t∈T.region)
    (hclose : ∃p∈T.region,‖p‖≤rmax (1/2)) : t<1/5 := by
  have hf := common_reach_feasible T ha hb
  have ht4 : t<4/5 := by nlinarith
  have ht1 : t<1 := by linarith
  have hs := rho_gt_safe_radius ht ht1
  obtain ⟨p,hp,hpn⟩ := hclose
  have hnorm := actual_common_reach_separation T ht.le hu ha hb p hp
  have hsmall := rmax_half_lt_two_twentyfive
  by_contra hn
  have hz : 4/25≤t*(1-t) := by
    nlinarith [mul_nonneg (show 0≤t-1/5 by linarith) (show 0≤4/5-t by linarith)]
  linarith

theorem ray_shorter_mem (T : UnitTriangle) (e : Plane) {a t : ℝ}
    (ha0 : 0<a) (ht0 : 0≤t) (hta : t≤a)
    (hu : corner∈T.region) (ha : corner+a • e∈T.region) : corner+t • e∈T.region := by
  have hrat0 : 0≤t/a := div_nonneg ht0 ha0.le
  have hrat1 : t/a≤1 := (div_le_one ha0).mpr hta
  have hm := T.convex_region hu ha (sub_nonneg.mpr hrat1) hrat0 (by ring : 1-t/a+t/a=1)
  have he : (1-t/a) • corner+(t/a) • (corner+a • e)=corner+t • e := by
    calc
      _ = (1-t/a) • corner+(t/a) • corner+((t/a)*a) • e := by module
      _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt ha0)]; module
  rwa [he] at hm

/-- The minimum of the actual two reaches supplies the same common corner. -/
theorem actual_min_reach_separation (T : UnitTriangle) {a b : ℝ}
    (ha0 : 0<a) (hb0 : 0<b) (hu : corner∈T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region) :
    ∀p∈T.region,rho (min a b)≤‖p‖ := by
  have ht : 0 < min a b := lt_min ha0 hb0
  have hA := ray_shorter_mem T upperRay ha0 ht.le (min_le_left a b) hu ha
  have hB := ray_shorter_mem T lowerRay hb0 ht.le (min_le_right a b) hu hb
  exact actual_common_reach_separation T ht.le hu hA hB

theorem actual_min_reach_small (T : UnitTriangle) {a b : ℝ}
    (ha0 : 0<a) (hb0 : 0<b) (hu : corner∈T.region)
    (ha : upperEndpoint a∈T.region) (hb : lowerEndpoint b∈T.region)
    (hclose : ∃p∈T.region,‖p‖≤rmax (1/2)) : min a b<1/5 := by
  have ht : 0 < min a b := lt_min ha0 hb0
  have hA := ray_shorter_mem T upperRay ha0 ht.le (min_le_left a b) hu ha
  have hB := ray_shorter_mem T lowerRay hb0 ht.le (min_le_right a b) hu hb
  exact actual_common_reach_small T ht hu hA hB hclose

end
end HexagonCover.IntruderReach
