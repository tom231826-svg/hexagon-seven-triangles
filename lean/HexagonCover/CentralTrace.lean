import HexagonCover.TraceAlgebra
import HexagonCover.CornerTransport

/-! Actual finite central traces: geometry before the scalar cap estimate.
All vertices and barycentric coefficients belong to one actual UnitTriangle. -/
namespace HexagonCover.CentralTrace
noncomputable section
open TriangleFrame
local notation "h₀" => NICertificate.halfRoot

theorem weight_nonneg (T : UnitTriangle) {p : Plane} (hp : p∈T.region) (i : Fin 3) :
    0≤weight T p i :=
  div_nonneg (sub_nonneg.mpr ((mem_region_iff_halfplanes T p).mp hp i)) (by positivity)

theorem coord_reconstruct (T : UnitTriangle) (p : Plane) (k : Fin 2) :
    ∑i : Fin 3,weight T p i*(T.vertex i) k=p k := by
  have hs := weight_reconstruct T p
  rw [Fin.sum_univ_three] at hs ⊢
  have hc := congrArg (fun q : Plane => q k) hs
  simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] using hc

theorem coord_le (T : UnitTriangle) {p : Plane} (hp : p∈T.region) (k : Fin 2) {d : ℝ}
    (hv : ∀i,(T.vertex i) k≤d) : p k≤d := by
  have hm := Finset.sum_le_sum (s:=Finset.univ)
    (fun (i:Fin 3) _ => mul_le_mul_of_nonneg_left (hv i) (weight_nonneg T hp i))
  rw [coord_reconstruct,←Finset.sum_mul,weight_sum,one_mul] at hm
  exact hm

theorem le_coord (T : UnitTriangle) {p : Plane} (hp : p∈T.region) (k : Fin 2) {d : ℝ}
    (hv : ∀i,d≤(T.vertex i) k) : d≤p k := by
  have hm := Finset.sum_le_sum (s:=Finset.univ)
    (fun (i:Fin 3) _ => mul_le_mul_of_nonneg_left (hv i) (weight_nonneg T hp i))
  rw [coord_reconstruct,←Finset.sum_mul,weight_sum,one_mul] at hm
  exact hm

theorem origin_weight_lower (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) (i : Fin 3) : r/h₀≤weight T 0 i := by
  have hoff := CentralRadius.offset_ge_radius T hr hball i
  unfold weight
  simp only [dotp,PiLp.zero_apply,mul_zero,add_zero,sub_zero]
  exact div_le_div_of_nonneg_right hoff ExtremeTriangle.halfRoot_pos.le

theorem exists_low_vertex (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) : ∃i,(T.vertex i) 1≤-r := by
  have hn : ‖point 0 (-r)‖=r := by
    have hs := norm_point_sq 0 (-r)
    nlinarith [norm_nonneg (point 0 (-r))]
  have hp : point 0 (-r)∈T.region := by
    apply hball
    rw [Metric.mem_closedBall,dist_zero_right,hn]
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ (fun i : Fin 3 => (T.vertex i) 1)
    Finset.univ_nonempty
  exact ⟨i,le_coord T hp 1 (fun j => hi j (Finset.mem_univ j))⟩

/-- A positive central disk rules out two vertices at or above an edge line. -/
theorem high_vertex_unique (T : UnitTriangle) {r : ℝ} (hr : 0<r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) {i j : Fin 3}
    (hi : h₀≤(T.vertex i) 1) (hj : h₀≤(T.vertex j) 1) : i=j := by
  by_contra hij
  obtain ⟨k,hk⟩ := exists_low_vertex T hr.le hball
  have hh := ExtremeTriangle.halfRoot_pos
  have hik : i≠k := by intro he; subst k; linarith
  have hjk : j≠k := by intro he; subst k; linarith
  have h1 := dist_sq_coordinates (T.vertex i) (T.vertex k)
  have h2 := dist_sq_coordinates (T.vertex j) (T.vertex k)
  have h3 := dist_sq_coordinates (T.vertex i) (T.vertex j)
  rw [T.edgeLength i k hik] at h1
  rw [T.edgeLength j k hjk] at h2
  rw [T.edgeLength i j hij] at h3
  have he : ((T.vertex i) 0+(T.vertex j) 0-2*(T.vertex k) 0)^2+
      ((T.vertex i) 1+(T.vertex j) 1-2*(T.vertex k) 1)^2=3 := by nlinarith only [h1,h2,h3]
  have hv : 2*h₀<(T.vertex i) 1+(T.vertex j) 1-2*(T.vertex k) 1 := by linarith
  have hs : (2*h₀)^2<((T.vertex i) 1+(T.vertex j) 1-2*(T.vertex k) 1)^2 :=
    (sq_lt_sq₀ (by positivity) (by linarith)).mpr hv
  nlinarith [ExtremeTriangle.halfRoot_sq,
    sq_nonneg ((T.vertex i) 0+(T.vertex j) 0-2*(T.vertex k) 0)]

def relabel (T : UnitTriangle) (σ : Equiv.Perm (Fin 3)) : UnitTriangle where
  vertex i := T.vertex (σ i)
  edgeLength i j hij := T.edgeLength (σ i) (σ j) (σ.injective.ne hij)

theorem relabel_region (T : UnitTriangle) (σ : Equiv.Perm (Fin 3)) :
    (relabel T σ).region=T.region := by
  unfold UnitTriangle.region
  congr 1
  ext p
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨σ i,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨σ.symm i,by simp [relabel]⟩

/-- At a unique highest vertex, the level set at its exact height is a point. -/
theorem point_at_unique_max (T : UnitTriangle) (k : Fin 3)
    (hmax : ∀i,(T.vertex i) 1≤(T.vertex k) 1)
    (huniq : ∀i,(T.vertex i) 1=(T.vertex k) 1 → i=k)
    {p : Plane} (hp : p∈T.region) (hpy : p 1=(T.vertex k) 1) : p=T.vertex k := by
  have hw := weight_nonneg T hp
  have hsum : (∑i : Fin 3,weight T p i*((T.vertex k) 1-(T.vertex i) 1))=0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,weight_sum,one_mul,coord_reconstruct,hpy,sub_self]
  have hzero : ∀i,weight T p i*((T.vertex k) 1-(T.vertex i) 1)=0 := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (i:Fin 3) _ => mul_nonneg (hw i) (sub_nonneg.mpr (hmax i)))).mp hsum
    exact fun i => he i (Finset.mem_univ i)
  have hweight : ∀i,i≠k → weight T p i=0 := by
    intro i hik
    have hne : (T.vertex k) 1-(T.vertex i) 1≠0 := by
      intro he
      apply hik
      apply huniq
      linarith
    exact (mul_eq_zero.mp (hzero i)).resolve_right hne
  have hwk : weight T p k=1 := by
    have he : ∑i : Fin 3,weight T p i=weight T p k := by
      apply Finset.sum_eq_single k
      · intro i _ hik; exact hweight i hik
      · simp
    rw [weight_sum] at he
    exact he.symm
  have he : ∑i : Fin 3,weight T p i • T.vertex i=weight T p k • T.vertex k := by
    apply Finset.sum_eq_single k
    · intro i _ hik; rw [hweight i hik,zero_smul]
    · simp
  rw [weight_reconstruct,hwk,one_smul] at he
  exact he

/-- Two distinct actual trace points force an actual vertex strictly above h. -/
theorem exists_top_vertex (T : UnitTriangle) {r : ℝ} (hr : 0<r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) {p q : Plane}
    (hp : p∈T.region) (hq : q∈T.region) (hpy : p 1=h₀) (hqy : q 1=h₀) (hpq : p≠q) :
    ∃k,h₀<(T.vertex k) 1 ∧ ∀i,i≠k → (T.vertex i) 1<h₀ := by
  obtain ⟨k,_,hk⟩ := Finset.exists_max_image Finset.univ (fun i : Fin 3 => (T.vertex i) 1)
    Finset.univ_nonempty
  have hmax : ∀i,(T.vertex i) 1≤(T.vertex k) 1 := fun i => hk i (Finset.mem_univ i)
  have hkge : h₀≤(T.vertex k) 1 := by rw [←hpy]; exact coord_le T hp 1 hmax
  have huniq : ∀i,(T.vertex i) 1=(T.vertex k) 1 → i=k := by
    intro i he
    exact high_vertex_unique T hr hball (by rw [he]; exact hkge) hkge
  have htop : h₀<(T.vertex k) 1 := by
    by_contra hn
    have hke : (T.vertex k) 1=h₀ := le_antisymm (le_of_not_gt hn) hkge
    have hp' := point_at_unique_max T k hmax huniq hp (hpy.trans hke.symm)
    have hq' := point_at_unique_max T k hmax huniq hq (hqy.trans hke.symm)
    exact hpq (hp'.trans hq'.symm)
  refine ⟨k,htop,?_⟩
  intro i hik
  by_contra hn
  exact hik (high_vertex_unique T hr hball (le_of_not_gt hn) hkge)


theorem edge_reconstruct (T : UnitTriangle) (p : Plane) :
    p-T.vertex 0=weight T p 1 • (T.vertex 1-T.vertex 0)+
      weight T p 2 • (T.vertex 2-T.vertex 0) := by
  have hs := weight_sum T p
  have hp := weight_reconstruct T p
  rw [Fin.sum_univ_three] at hs hp
  calc
    _ = weight T p 0 • T.vertex 0+weight T p 1 • T.vertex 1+weight T p 2 • T.vertex 2-
        (weight T p 0+weight T p 1+weight T p 2) • T.vertex 0 := by rw [hp,hs,one_smul]
    _ = _ := by module

theorem edge_coordinates (T : UnitTriangle) (p : Plane) (k : Fin 2) :
    p k-(T.vertex 0) k=weight T p 1*((T.vertex 1) k-(T.vertex 0) k)+
      weight T p 2*((T.vertex 2) k-(T.vertex 0) k) := by
  have he := congrArg (fun q : Plane => q k) (edge_reconstruct T p)
  simpa only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] using he

theorem edge_gram (T : UnitTriangle) :
    dotp (T.vertex 1-T.vertex 0) (T.vertex 1-T.vertex 0)=1 ∧
    dotp (T.vertex 2-T.vertex 0) (T.vertex 2-T.vertex 0)=1 ∧
    dotp (T.vertex 1-T.vertex 0) (T.vertex 2-T.vertex 0)=1/2 := by
  have h1 : ‖T.vertex 1-T.vertex 0‖=1 := by rw [←dist_eq_norm,T.edgeLength 1 0 (by decide)]
  have h2 : ‖T.vertex 2-T.vertex 0‖=1 := by rw [←dist_eq_norm,T.edgeLength 2 0 (by decide)]
  have he := CommonReach.polarization (T.vertex 1) (T.vertex 2) (T.vertex 0)
  rw [T.edgeLength 1 0 (by decide),T.edgeLength 2 0 (by decide),T.edgeLength 1 2 (by decide)] at he
  exact ⟨by rw [←CommonReach.norm_sq,h1]; norm_num,
    by rw [←CommonReach.norm_sq,h2]; norm_num,by linarith⟩

theorem edge_det_abs {u w : Plane} (hu : dotp u u=1) (hw : dotp w w=1)
    (huw : dotp u w=1/2) : |u 0*w 1-u 1*w 0|=h₀ := by
  have he : (u 0*w 1-u 1*w 0)^2=dotp u u*dotp w w-(dotp u w)^2 := by unfold dotp; ring
  rw [hu,hw,huw] at he
  apply (sq_eq_sq₀ (abs_nonneg _) ExtremeTriangle.halfRoot_pos.le).mp
  rw [sq_abs,ExtremeTriangle.halfRoot_sq]
  nlinarith

/-- Ordering the two downward drops gives the cap chart, irrespective of the
horizontal signs of the actual edges. -/
theorem drops_chart {u w : Plane} (hu : dotp u u=1) (hw : dotp w w=1)
    (huw : dotp u w=1/2) (hs : 0 < -w 1) (horder : -w 1 ≤ -u 1) :
    1/2 ≤ |w 0| ∧ (|w 0|)^2+(-w 1)^2=1 ∧ -u 1=h₀*|w 0|+(-w 1)/2 := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hunit : (|w 0|)^2+(-w 1)^2=1 := by simpa [dotp,pow_two,sq_abs] using hw
  have hchart : -u 1=h₀*|w 0|+(-w 1)/2 := by
    have hn := ExtremeTriangle.other_normal_eq
      (c:=w 0) (s:=w 1) (u:= -u 0) (v:= -u 1)
      (by dsimp [dotp] at hw; nlinarith) (by dsimp [dotp] at hu; nlinarith)
      (by dsimp [dotp] at huw; nlinarith)
    rcases hn with he | he
    · have hy := congrArg Prod.snd he
      norm_num [NICertificate.normalValues] at hy
      have hx : 0 ≤ w 0 := by nlinarith
      rw [abs_of_nonneg hx]
      linarith
    · have hy := congrArg Prod.snd he
      norm_num [NICertificate.normalValues] at hy
      have hx : w 0 ≤ 0 := by nlinarith
      rw [abs_of_nonpos hx]
      linarith
  have hineq : -w 1 ≤ 2*h₀*|w 0| := by linarith
  have hsq : (-w 1)^2 ≤ (2*h₀*|w 0|)^2 :=
    (sq_le_sq₀ hs.le (by positivity)).mpr hineq
  have hm := congrArg (fun z : ℝ => 4*(|w 0|)^2*z) ExtremeTriangle.halfRoot_sq
  refine ⟨?_,hunit,hchart⟩
  nlinarith [abs_nonneg (w 0)]

theorem same_height_dist (p q : Plane) (hy : p 1=q 1) : dist p q=|p 0-q 0| := by
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  rw [dist_sq_coordinates,sq_abs,hy,sub_self,zero_pow (by decide),add_zero]

/-- Finite-side cap width, derived from actual barycentric coefficients. -/
theorem actual_cap_width (T : UnitTriangle)
    (htop : h₀ < (T.vertex 0) 1) (hl1 : (T.vertex 1) 1 < h₀) (hl2 : (T.vertex 2) 1 < h₀)
    {p q : Plane} (hp : p∈T.region) (hq : q∈T.region) (hpy : p 1=h₀) (hqy : q 1=h₀) :
    dist p q ≤ h₀*((T.vertex 0) 1-h₀)/
      (((T.vertex 0) 1-(T.vertex 1) 1)*((T.vertex 0) 1-(T.vertex 2) 1)) := by
  let d1 := (T.vertex 0) 1-(T.vertex 1) 1
  let d2 := (T.vertex 0) 1-(T.vertex 2) 1
  let Y := (T.vertex 0) 1
  let ux := (T.vertex 1) 0-(T.vertex 0) 0
  let wx := (T.vertex 2) 0-(T.vertex 0) 0
  have hd1 : 0<d1 := by dsimp [d1]; linarith
  have hd2 : 0<d2 := by dsimp [d2]; linarith
  have hyP : weight T p 1*d1+weight T p 2*d2=Y-h₀ := by
    have hh := edge_coordinates T p 1
    rw [hpy] at hh
    dsimp [d1,d2,Y]
    linarith
  have hyQ : weight T q 1*d1+weight T q 2*d2=Y-h₀ := by
    have hh := edge_coordinates T q 1
    rw [hqy] at hh
    dsimp [d1,d2,Y]
    linarith
  have hbP : weight T p 1*d1 ≤ Y-h₀ := by
    nlinarith only [hyP,mul_nonneg (weight_nonneg T hp 2) hd2.le]
  have hbQ : weight T q 1*d1 ≤ Y-h₀ := by
    nlinarith only [hyQ,mul_nonneg (weight_nonneg T hq 2) hd2.le]
  have hbound : d1*|weight T p 1-weight T q 1| ≤ Y-h₀ := by
    rw [←abs_of_pos hd1,←abs_mul]
    apply abs_le.mpr
    constructor
    · nlinarith only [hbQ,mul_nonneg (weight_nonneg T hp 1) hd1.le]
    · nlinarith only [hbP,mul_nonneg (weight_nonneg T hq 1) hd1.le]
  have hxP : p 0-(T.vertex 0) 0=weight T p 1*ux+weight T p 2*wx := edge_coordinates T p 0
  have hxQ : q 0-(T.vertex 0) 0=weight T q 1*ux+weight T q 2*wx := edge_coordinates T q 0
  have he : d2*(p 0-q 0)=(weight T p 1-weight T q 1)*(ux*d2-wx*d1) := by
    nlinarith only [congrArg (fun z : ℝ => d2*z) hxP,congrArg (fun z : ℝ => d2*z) hxQ,
      congrArg (fun z : ℝ => wx*z) hyP,congrArg (fun z : ℝ => wx*z) hyQ]
  have hg := edge_gram T
  have hdet : |ux*d2-wx*d1|=h₀ := by
    have hh := edge_det_abs hg.1 hg.2.1 hg.2.2
    have hf : ux*d2-wx*d1 =
        -((T.vertex 1-T.vertex 0) 0*(T.vertex 2-T.vertex 0) 1-
          (T.vertex 1-T.vertex 0) 1*(T.vertex 2-T.vertex 0) 0) := by
      dsimp [ux,wx,d1,d2]; ring
    rw [hf,abs_neg,hh]
  have heabs := congrArg abs he
  rw [abs_mul,abs_of_pos hd2,abs_mul,hdet,←same_height_dist p q (hpy.trans hqy.symm)] at heabs
  apply (le_div_iff₀ (mul_pos hd1 hd2)).mpr
  change dist p q*(d1*d2) ≤ h₀*(Y-h₀)
  have hm := mul_le_mul_of_nonneg_right hbound ExtremeTriangle.halfRoot_pos.le
  nlinarith only [hm,congrArg (fun z : ℝ => d1*z) heabs]


/-- The actual disk's barycentric lower bounds constrain the top height. -/
theorem actual_top_height (T : UnitTriangle) {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall (0:Plane) r ⊆ T.region)
    (htop : h₀ < (T.vertex 0) 1) (hl2 : (T.vertex 2) 1 < h₀)
    (horder : (T.vertex 1) 1 ≤ (T.vertex 2) 1) :
    (T.vertex 0) 1 ≤ (T.vertex 0) 1-(T.vertex 1) 1-
      2*r*|(T.vertex 2) 0-(T.vertex 0) 0| := by
  let d1 := (T.vertex 0) 1-(T.vertex 1) 1
  let d2 := (T.vertex 0) 1-(T.vertex 2) 1
  let c := |(T.vertex 2) 0-(T.vertex 0) 0|
  have hd1 : 0 ≤ d1 := by dsimp [d1]; linarith
  have hd12 : 0 ≤ d1-d2 := by dsimp [d1,d2]; linarith
  have hg := edge_gram T
  have hc := (drops_chart hg.1 hg.2.1 hg.2.2
    (by simp only [PiLp.sub_apply]; linarith)
    (by simp only [PiLp.sub_apply]; linarith)).2.2
  have hc' : d1=h₀*c+d2/2 := by simpa [d1,d2,c] using hc
  have hw0 := mul_le_mul_of_nonneg_right (origin_weight_lower T hr hball 0) hd1
  have hw2 := mul_le_mul_of_nonneg_right (origin_weight_lower T hr hball 2) hd12
  have hs := weight_sum T (0:Plane)
  rw [Fin.sum_univ_three] at hs
  have hy : (T.vertex 0) 1=weight T 0 1*d1+weight T 0 2*d2 := by
    have he := edge_coordinates T 0 1
    simp only [PiLp.zero_apply] at he
    dsimp [d1,d2]
    linarith
  have he : r/h₀*(2*d1-d2)=2*r*c := by
    rw [hc']
    field_simp [ne_of_gt ExtremeTriangle.halfRoot_pos]
    <;> ring
  change (T.vertex 0) 1 ≤ d1-2*r*c
  nlinarith only [hw0,hw2,hy,he,congrArg (fun z : ℝ => d1*z) hs]

/-- Actual cap estimate with the three vertices only reordered by height. -/
theorem ordered_trace (T : UnitTriangle) {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall (0:Plane) r ⊆ T.region)
    (htop : h₀ < (T.vertex 0) 1) (hl2 : (T.vertex 2) 1 < h₀)
    (horder : (T.vertex 1) 1 ≤ (T.vertex 2) 1)
    {p q : Plane} (hp : p∈T.region) (hq : q∈T.region) (hpy : p 1=h₀) (hqy : q 1=h₀) :
    dist p q ≤ 1/2-Real.sqrt (8*h₀*r/3) := by
  have hg := edge_gram T
  have hc := drops_chart hg.1 hg.2.1 hg.2.2
    (by simp only [PiLp.sub_apply]; linarith)
    (by simp only [PiLp.sub_apply]; linarith)
  let c := |(T.vertex 2) 0-(T.vertex 0) 0|
  let s := (T.vertex 0) 1-(T.vertex 2) 1
  have hc0 : 1/2 ≤ c := hc.1
  have hunit : c^2+s^2=1 := by simpa [c,s] using hc.2.1
  have hd : (T.vertex 0) 1-(T.vertex 1) 1=h₀*c+s/2 := by simpa [c,s] using hc.2.2
  have hheight := actual_top_height T hr hball htop hl2 horder
  have hbound := TraceAlgebra.cap_bound (Y := (T.vertex 0) 1) hc0 (by dsimp [s]; linarith) hunit hr
    (by rw [←hd]; exact hheight)
  have hcap := actual_cap_width T htop (horder.trans_lt hl2) hl2 hp hq hpy hqy
  rw [hd] at hcap
  exact hcap.trans hbound

/-- If an actual central triangle reaches the edge line at all, the proposed
trace bound is nonnegative, including a singleton intersection. -/
theorem trace_bound_nonneg (T : UnitTriangle) {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall (0:Plane) r ⊆ T.region)
    {p : Plane} (hp : p∈T.region) (hpy : p 1=h₀) :
    0 ≤ 1/2-Real.sqrt (8*h₀*r/3) := by
  have hn : 1-(1/2:ℝ)+(1/2:ℝ)^2 ≤ ‖p‖^2 := by
    rw [CommonReach.norm_sq]
    unfold dotp
    rw [hpy]
    nlinarith [sq_nonneg (p 0),ExtremeTriangle.halfRoot_sq]
  have hrmax := CentralRadius.actual_endpoint_radius T hr hball hp hn
  have hrsmall := hrmax.trans_lt IntruderReach.rmax_half_lt_two_twentyfive
  have hh := ExtremeTriangle.halfRoot_pos
  have hh1 : h₀ ≤ 1 := by nlinarith [ExtremeTriangle.halfRoot_sq]
  have hm := mul_le_mul_of_nonneg_right hh1 hr
  have hs : Real.sqrt (8*h₀*r/3) ≤ (1/2:ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ 8*h₀*r/3)]
    nlinarith
  linarith

/-- Every actual pair on the horizontal hexagon edge line satisfies the sharp
source trace estimate. No orientation, vertex-order or intrusion premise. -/
theorem horizontal_trace (T : UnitTriangle) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0:Plane) r ⊆ T.region)
    {p q : Plane} (hp : p∈T.region) (hq : q∈T.region) (hpy : p 1=h₀) (hqy : q 1=h₀) :
    dist p q ≤ 1/2-Real.sqrt (8*h₀*r/3) := by
  by_cases hpq : p=q
  · subst q
    rw [dist_self]
    exact trace_bound_nonneg T hr.le hball hp hpy
  obtain ⟨k,hk,hl⟩ := exists_top_vertex T hr hball hp hq hpy hqy hpq
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 k
  let T' := relabel T σ
  have hregion : T'.region=T.region := relabel_region T σ
  have hzero : σ 0=k := by simp [σ]
  have ht : h₀ < (T'.vertex 0) 1 := by simpa [T',relabel,hzero] using hk
  have hlo : ∀i:Fin 3,i≠0 → (T'.vertex i) 1<h₀ := by
    intro i hi
    apply hl
    intro he
    apply hi
    exact σ.injective (he.trans hzero.symm)
  have hb : Metric.closedBall (0:Plane) r ⊆ T'.region := by rw [hregion]; exact hball
  have hp' : p∈T'.region := by rw [hregion]; exact hp
  have hq' : q∈T'.region := by rw [hregion]; exact hq
  by_cases ho : (T'.vertex 1) 1 ≤ (T'.vertex 2) 1
  · exact ordered_trace T' hr.le hb ht (hlo 2 (by decide)) ho hp' hq' hpy hqy
  let T'' := relabel T' (Equiv.swap 1 2)
  have hregion' : T''.region=T'.region := relabel_region T' _
  have he0 : (Equiv.swap (1:Fin 3) 2) 0=0 := by decide
  apply ordered_trace T'' hr.le
    (by rw [hregion']; exact hb)
    (by simpa only [T'',relabel,he0] using ht)
    (by simpa [T'',relabel] using hlo 1 (by decide))
    (by simpa [T'',relabel] using (le_of_not_ge ho))
    (by rw [hregion']; exact hp') (by rw [hregion']; exact hq') hpy hqy

/-- A symmetry fixing the origin transports the actual closed disk. -/
theorem action_closedBall (a : QSymmetry.Action) (T : UnitTriangle) {r : ℝ}
    (hball : Metric.closedBall (0:Plane) r ⊆ T.region) :
    Metric.closedBall (0:Plane) r ⊆ (Symmetry.mapTriangle a.motion T).region := by
  intro p hp
  rw [Symmetry.map_region]
  refine ⟨a.motion.symm p,hball ?_,a.motion.apply_symm_apply p⟩
  rw [Metric.mem_closedBall,dist_zero_right] at hp ⊢
  have hn := a.norm (a.motion.symm p)
  rw [a.motion.apply_symm_apply] at hn
  exact hn ▸ hp

/-- Any two points of the same actual triangle on any hexagon edge line satisfy
the finite-side trace estimate. Parameters need not lie in the finite edge. -/
theorem edge_trace (T : UnitTriangle) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0:Plane) r ⊆ T.region) (i : Fin 6) {t u : ℝ}
    (ht : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t ∈ T.region)
    (hu : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) u ∈ T.region) :
    dist (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t)
      (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) u) ≤
        1/2-Real.sqrt (8*h₀*r/3) := by
  let a := QSymmetry.rotationPower ((1-i : Fin 6).val)
  let T' := Symmetry.mapTriangle a.motion T
  have hline (v : ℝ) :
      (a.motion (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) v)) 1=h₀ := by
    rw [CornerTransport.action_lineMap]
    have he1 : i+(1-i)= (1:Fin 6) := by fin_cases i <;> decide
    have he2 : (i+1)+(1-i)= (2:Fin 6) := by fin_cases i <;> decide
    dsimp [a]
    rw [CornerTransport.rotationPower_vertex,CornerTransport.rotationPower_vertex,he1,he2]
    simp [AffineMap.lineMap_apply,hexVertex,NICertificate.halfRoot]
  have hmem {v : ℝ} (hv : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) v ∈ T.region) :
      a.motion (AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) v) ∈ T'.region := by
    rw [Symmetry.map_region]
    exact ⟨_,hv,rfl⟩
  have hb := horizontal_trace T' hr (action_closedBall a T hball)
    (hmem ht) (hmem hu) (hline t) (hline u)
  rw [a.motion.isometry.dist_eq] at hb
  exact hb

/-- Unit edge coordinates turn the actual geometric trace bound into a bound
on its parameter interval length. -/
theorem edge_parameter_trace (T : UnitTriangle) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0:Plane) r ⊆ T.region) (i : Fin 6) {t u : ℝ}
    (ht : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t ∈ T.region)
    (hu : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) u ∈ T.region) :
    |t-u| ≤ 1/2-Real.sqrt (8*h₀*r/3) := by
  have he : dist (hexVertex 1 i) (hexVertex 1 (i+1))=1 :=
    (StandardCover.fan i).edgeLength 1 2 (by decide)
  have hb := edge_trace T hr hball i ht hu
  rw [dist_lineMap_lineMap,he,mul_one,Real.dist_eq] at hb
  exact hb

end
end HexagonCover.CentralTrace
