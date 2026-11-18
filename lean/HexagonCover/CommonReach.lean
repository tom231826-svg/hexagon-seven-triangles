import HexagonCover.HeavyReach

/-! Sharp common-reach separation for the same actual finite triangle.
Source exposure and fresh algebra are recorded in reach-geometry-exposure.md. -/

namespace HexagonCover.CommonReach
noncomputable section
open TriangleFrame ExteriorLoss

theorem norm_sq (p : Plane) : ‖p‖ ^ 2 = dotp p p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotp, Fin.sum_univ_two, pow_two]

theorem polarization (p q v : Plane) :
    2 * dotp (p-v) (q-v) = dist p v ^ 2 + dist q v ^ 2 - dist p q ^ 2 := by
  simp only [dist_sq_coordinates, dotp, PiLp.sub_apply]
  ring

def coneRelation (v p q : Plane) : Prop :=
  ‖p-v‖ * ‖q-v‖ ≤ 2 * dotp (p-v) (q-v)

theorem coneRelation_symm {v p q : Plane} (h : coneRelation v p q) :
    coneRelation v q p := by
  simpa only [coneRelation, mul_comm, dotp_comm] using h

theorem coneRelation_convex (v q : Plane) : Convex ℝ {p | coneRelation v p q} := by
  intro p hp z hz a b ha hb hab
  change coneRelation v p q at hp
  change coneRelation v z q at hz
  change ‖a • p + b • z - v‖ * ‖q-v‖ ≤ 2 * dotp (a • p+b • z-v) (q-v)
  have he : a • p+b • z-v = a • (p-v)+b • (z-v) := by
    calc
      _ = a • p+b • z-(a+b) • v := by rw [hab,one_smul]
      _ = _ := by module
  rw [he]
  have hn : ‖a • (p-v)+b • (z-v)‖ ≤ a*‖p-v‖+b*‖z-v‖ := by
    calc
      _ ≤ ‖a • (p-v)‖ + ‖b • (z-v)‖ := norm_add_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  calc
    _ ≤ (a*‖p-v‖+b*‖z-v‖)*‖q-v‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = a*(‖p-v‖*‖q-v‖)+b*(‖z-v‖*‖q-v‖) := by ring
    _ ≤ a*(2*dotp (p-v) (q-v))+b*(2*dotp (z-v) (q-v)) :=
      add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hz hb)
    _ = _ := by simp only [dotp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem vertex_cone (T : UnitTriangle) (i j k : Fin 3) :
    coneRelation (T.vertex k) (T.vertex i) (T.vertex j) := by
  by_cases hik : i=k
  · subst i; simp [coneRelation, dotp]
  by_cases hjk : j=k
  · subst j; simp [coneRelation, dotp]
  have hi : ‖T.vertex i-T.vertex k‖=1 := by
    rw [← dist_eq_norm, T.edgeLength i k hik]
  have hj : ‖T.vertex j-T.vertex k‖=1 := by
    rw [← dist_eq_norm, T.edgeLength j k hjk]
  have hpol := polarization (T.vertex i) (T.vertex j) (T.vertex k)
  rw [T.edgeLength i k hik, T.edgeLength j k hjk] at hpol
  unfold coneRelation
  rw [hi,hj]
  by_cases hij : i=j
  · subst j; simp only [dist_self] at hpol; nlinarith
  · rw [T.edgeLength i j hij] at hpol; nlinarith

/-- All points of the actual triangle lie in each vertex's sixty-degree cone. -/
theorem actual_vertex_cone (T : UnitTriangle) (k : Fin 3) {p q : Plane}
    (hp : p∈T.region) (hq : q∈T.region) : coneRelation (T.vertex k) p q := by
  have hv (i : Fin 3) : ∀ q∈T.region, coneRelation (T.vertex k) (T.vertex i) q := by
    intro q hq
    apply coneRelation_symm
    exact (convexHull_min (by rintro _ ⟨j,rfl⟩; exact vertex_cone T j i k)
      (coneRelation_convex (T.vertex k) (T.vertex i))) hq
  exact (convexHull_min (by rintro _ ⟨i,rfl⟩; exact hv i q hq)
    (coneRelation_convex (T.vertex k) q)) hp

theorem endpoint_cone_distance {t : ℝ} (ht : 0≤t) (v : Plane)
    (hc : coneRelation v (upperEndpoint t) (lowerEndpoint t)) :
    t ≤ dist corner v := by
  let X := v 0 - 1
  let Y := v 1
  let R := X^2+Y^2
  let D := R+t*X-t^2/2
  have hs := ExtremeTriangle.halfRoot_sq
  have hd : dotp (upperEndpoint t-v) (lowerEndpoint t-v)=D := by
    dsimp [dotp, upperEndpoint, lowerEndpoint, corner, upperRay, lowerRay, D, R, X, Y]
    nlinarith only [congrArg (fun z : ℝ => t^2*z) hs]
  have hD0 : 0≤D := by
    have hn := mul_nonneg (norm_nonneg (upperEndpoint t-v)) (norm_nonneg (lowerEndpoint t-v))
    rw [coneRelation, hd] at hc
    linarith
  have hc2 : (‖upperEndpoint t-v‖ * ‖lowerEndpoint t-v‖)^2 ≤ 4*D^2 := by
    rw [coneRelation, hd] at hc
    have hn := mul_nonneg (norm_nonneg (upperEndpoint t-v)) (norm_nonneg (lowerEndpoint t-v))
    have hh : (‖upperEndpoint t-v‖*‖lowerEndpoint t-v‖)^2≤(2*D)^2 :=
      (sq_le_sq₀ hn (by positivity)).mpr hc
    nlinarith only [hh]
  have hid : ‖upperEndpoint t-v‖^2 * ‖lowerEndpoint t-v‖^2 - D^2 =
      3*t^2*(X+t/2)^2 := by
    rw [norm_sq, norm_sq]
    dsimp [dotp, upperEndpoint, lowerEndpoint, corner, upperRay, lowerRay, D, R, X, Y]
    nlinarith only [congrArg (fun z : ℝ =>
      t^4*z^2 + (2*t^2*(v 0-1)^2+2*t^3*(v 0-1)+t^4/2-2*t^2*(v 1)^2)*z) hs]
  have hsq : t^2*(X+t/2)^2 ≤ D^2 := by nlinarith only [hid,hc2]
  have hR : t^2≤R := by
    by_cases hX : 0≤X+t/2
    · have hh : 0≤t*(X+t/2) := mul_nonneg ht hX
      have hhD : t*(X+t/2)≤D :=
        (sq_le_sq₀ hh hD0).mp (by nlinarith only [hsq])
      dsimp [D] at hhD
      linarith only [hhD]
    · have hXle : X+t/2≤0 := by linarith only [hX]
      have hh : 0≤-t*(X+t/2) := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ht) hXle
      have hhD : -t*(X+t/2)≤D :=
        (sq_le_sq₀ hh hD0).mp (by nlinarith only [hsq])
      dsimp [D] at hhD
      nlinarith only [hhD, mul_nonpos_of_nonneg_of_nonpos ht hXle]
  have hr : dist corner v ^ 2 = R := by
    rw [dist_sq_coordinates]
    simp only [corner, point_coord_zero, point_coord_one]
    dsimp [R,X,Y]
    ring
  nlinarith only [hr,hR,ht,dist_nonneg (x:=corner) (y:=v)]

/-- The endpoint pair forces every actual vertex to be at least t from U. -/
theorem vertices_away (T : UnitTriangle) {t : ℝ} (ht : 0≤t)
    (ha : upperEndpoint t∈T.region) (hb : lowerEndpoint t∈T.region) (i : Fin 3) :
    t≤dist corner (T.vertex i) :=
  endpoint_cone_distance ht _ (actual_vertex_cone T i ha hb)


def quad (a b : ℝ) : ℝ := a^2+a*b+b^2

def radiusSq (t : ℝ) : ℝ := 1-t+t^2

def rho (t : ℝ) : ℝ := 1-Real.sqrt (radiusSq t)

theorem radiusSq_pos (t : ℝ) : 0<radiusSq t := by
  dsimp [radiusSq]
  nlinarith [sq_nonneg (t-1/2)]

theorem quad_comm (a b : ℝ) : quad a b = quad b a := by unfold quad; ring

theorem large_weight_bound {a b c t : ℝ}
    (ha : 0≤a) (hb : 1/2<b) (hc : 0≤c) (hs : a+b+c=1)
    (ht : 0≤t) (hd : t^2≤quad a c) : quad b c≤radiusSq t := by
  let r := Real.sqrt (quad a c)
  have hq : 0≤quad a c := by unfold quad; positivity
  have hr0 : 0≤r := Real.sqrt_nonneg _
  have hrs : r^2=quad a c := Real.sq_sqrt hq
  have hac : a+c<1/2 := by linarith
  have hr : r≤a+c := by
    have hh : r^2≤(a+c)^2 := by dsimp [quad] at hrs; nlinarith [mul_nonneg ha hc]
    exact (sq_le_sq₀ hr0 (by positivity)).mp hh
  have htr : t≤r := (sq_le_sq₀ ht hr0).mp (hd.trans_eq hrs.symm)
  have hkr : r≤2*a+c := by
    have hh : r^2≤(2*a+c)^2 := by
      dsimp [quad] at hrs
      nlinarith [mul_nonneg ha hc]
    exact (sq_le_sq₀ hr0 (by positivity)).mp hh
  have hdist : quad b c=1-(2*a+c)+r^2 := by
    dsimp [quad] at hrs ⊢
    nlinarith [sq_nonneg (a+b+c-1)]
  have hmono : 1-r+r^2≤radiusSq t := by
    dsimp [radiusSq]
    nlinarith [mul_nonneg (sub_nonneg.mpr htr) (show 0≤1-r-t by linarith)]
  rw [hdist]
  linarith

/-- Exact finite-triangle radius algebra, including boundary and equal weights. -/
theorem scalar_radius_bound {a b c t : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hs : a+b+c=1) (ht : 0≤t)
    (hdb : t^2≤quad c a) (hdc : t^2≤quad a b) : quad b c≤radiusSq t := by
  by_cases hb' : 1/2<b
  · exact large_weight_bound ha hb' hc hs ht (by simpa only [quad_comm c a] using hdb)
  by_cases hc' : 1/2<c
  · rw [quad_comm b c]
    exact large_weight_bound ha hc' hb (by linarith) ht hdc
  have hbb : b^2≤b/2 := by nlinarith [mul_nonneg hb (show 0≤1/2-b by linarith)]
  have hcc : c^2≤c/2 := by nlinarith [mul_nonneg hc (show 0≤1/2-c by linarith)]
  have hbc : b*c≤1/4 := by
    nlinarith [mul_nonneg hb (show 0≤1/2-c by linarith)]
  dsimp [quad,radiusSq]
  nlinarith [sq_nonneg (t-1/2)]

theorem norm_combination_sq (p q : Plane) (a b : ℝ) :
    ‖a • p+b • q‖^2=a^2*‖p‖^2+2*a*b*dotp p q+b^2*‖q‖^2 := by
  simp only [norm_sq, dotp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem combination_vertex_dist (p v₀ v₁ v₂ : Plane) {a b c : ℝ}
    (hs : a+b+c=1) (hp : a • v₀+b • v₁+c • v₂=p)
    (h₀₁ : dist v₀ v₁=1) (h₀₂ : dist v₀ v₂=1) (h₁₂ : dist v₁ v₂=1) :
    dist p v₀^2=quad b c := by
  have he : p-v₀=b • (v₁-v₀)+c • (v₂-v₀) := by
    calc
      _ = a • v₀+b • v₁+c • v₂-(a+b+c) • v₀ := by rw [hp,hs,one_smul]
      _ = _ := by module
  have h₁ : ‖v₁-v₀‖=1 := by rw [←dist_eq_norm,dist_comm]; exact h₀₁
  have h₂ : ‖v₂-v₀‖=1 := by rw [←dist_eq_norm,dist_comm]; exact h₀₂
  have hd := polarization v₁ v₂ v₀
  rw [dist_comm v₁ v₀,dist_comm v₂ v₀,h₀₁,h₀₂,h₁₂] at hd
  rw [dist_eq_norm,he,norm_combination_sq,h₁,h₂]
  dsimp [quad]
  nlinarith [congrArg (fun z : ℝ => b*c*z) hd]

/-- A point of an actual unit triangle, away from each vertex by t, lies
within sqrt(1-t+t²) of every vertex. -/
theorem finite_triangle_radius (T : UnitTriangle) {u : Plane} {t : ℝ}
    (hu : u∈T.region) (ht : 0≤t) (haway : ∀i,t≤dist u (T.vertex i)) :
    ∀i,dist u (T.vertex i)≤Real.sqrt (radiusSq t) := by
  let a := weight T u 0
  let b := weight T u 1
  let c := weight T u 2
  have hw (i : Fin 3) : 0≤weight T u i :=
    div_nonneg (sub_nonneg.mpr ((mem_region_iff_halfplanes T u).mp hu i)) (by positivity)
  have ha : 0≤a := hw 0
  have hb : 0≤b := hw 1
  have hc : 0≤c := hw 2
  have hs : a+b+c=1 := by simpa only [Fin.sum_univ_three] using weight_sum T u
  have hp : a • T.vertex 0+b • T.vertex 1+c • T.vertex 2=u := by
    simpa only [Fin.sum_univ_three] using weight_reconstruct T u
  have hd₀ : dist u (T.vertex 0)^2=quad b c :=
    combination_vertex_dist u _ _ _ hs hp
      (T.edgeLength 0 1 (by decide)) (T.edgeLength 0 2 (by decide)) (T.edgeLength 1 2 (by decide))
  have hd₁ : dist u (T.vertex 1)^2=quad c a :=
    combination_vertex_dist u _ _ _ (by linarith : b+c+a=1)
      (by rw [←hp]; module : b • T.vertex 1+c • T.vertex 2+a • T.vertex 0=u)
      (T.edgeLength 1 2 (by decide)) (T.edgeLength 1 0 (by decide)) (T.edgeLength 2 0 (by decide))
  have hd₂ : dist u (T.vertex 2)^2=quad a b :=
    combination_vertex_dist u _ _ _ (by linarith : c+a+b=1)
      (by rw [←hp]; module : c • T.vertex 2+a • T.vertex 0+b • T.vertex 1=u)
      (T.edgeLength 2 0 (by decide)) (T.edgeLength 2 1 (by decide)) (T.edgeLength 0 1 (by decide))
  have he₀ : t^2≤quad b c := by rw [←hd₀]; exact (sq_le_sq₀ ht dist_nonneg).mpr (haway 0)
  have he₁ : t^2≤quad c a := by rw [←hd₁]; exact (sq_le_sq₀ ht dist_nonneg).mpr (haway 1)
  have he₂ : t^2≤quad a b := by rw [←hd₂]; exact (sq_le_sq₀ ht dist_nonneg).mpr (haway 2)
  have hrad := Real.sq_sqrt (radiusSq_pos t).le
  intro i
  apply (sq_le_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [hrad]
  fin_cases i
  · change dist u (T.vertex 0)^2≤radiusSq t
    rw [hd₀]; exact scalar_radius_bound ha hb hc hs ht he₁ he₂
  · change dist u (T.vertex 1)^2≤radiusSq t
    rw [hd₁]; exact scalar_radius_bound hb hc ha (by linarith) ht he₂ he₀
  · change dist u (T.vertex 2)^2≤radiusSq t
    rw [hd₂]; exact scalar_radius_bound hc ha hb (by linarith) ht he₀ he₁

/-- The radius conclusion applies to the entire closed triangle by convexity. -/
theorem finite_triangle_ball (T : UnitTriangle) {u : Plane} {t : ℝ}
    (hu : u∈T.region) (ht : 0≤t) (haway : ∀i,t≤dist u (T.vertex i)) :
    T.region⊆Metric.closedBall u (Real.sqrt (radiusSq t)) := by
  apply convexHull_min
  · rintro _ ⟨i,rfl⟩
    simpa only [Metric.mem_closedBall,dist_comm] using finite_triangle_radius T hu ht haway i
  · exact convex_closedBall _ _

/-- Sharp common-reach separation, for all orientations of the same actual
finite triangle. No positive anchor disk or NI assumption is required. -/
theorem actual_common_reach_separation (T : UnitTriangle) {t : ℝ} (ht : 0≤t)
    (hu : corner∈T.region) (ha : upperEndpoint t∈T.region) (hb : lowerEndpoint t∈T.region) :
    ∀p∈T.region,rho t≤‖p‖ := by
  have hball := finite_triangle_ball T hu ht (vertices_away T ht ha hb)
  intro p hp
  have hd : dist p corner≤Real.sqrt (radiusSq t) := hball hp
  have hn : ‖corner‖=1 := by
    have hs := norm_point_sq (1:ℝ) 0
    change ‖corner‖^2=_ at hs
    nlinarith [norm_nonneg corner]
  have htri := norm_le_norm_add_norm_sub p corner
  rw [hn] at htri
  rw [dist_eq_norm] at hd
  dsimp [rho]
  linarith

end
end HexagonCover.CommonReach
