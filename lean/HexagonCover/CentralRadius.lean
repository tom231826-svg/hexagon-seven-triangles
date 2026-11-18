import HexagonCover.IntruderReach

/-! A true contained disk bounds the entire actual central triangle.
The support margins and circumradius estimate are derived from its vertices. -/
namespace HexagonCover.CentralRadius
noncomputable section
open TriangleFrame

def boundSq (r : ℝ) : ℝ := 1-2*Real.sqrt 3*r+4*r^2

theorem boundSq_pos (r : ℝ) : 0<boundSq r := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  unfold boundSq
  nlinarith [sq_nonneg (r-Real.sqrt 3/4)]

theorem normal_norm (T : UnitTriangle) (i : Fin 3) : ‖normal T i‖=1 := by
  have hg := normal_gram T i i
  rw [if_pos rfl,←CommonReach.norm_sq] at hg
  nlinarith [norm_nonneg (normal T i)]

/-- Actual closed disk containment bounds every derived support offset. -/
theorem offset_ge_radius (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) (i : Fin 3) : r≤offset T i := by
  have hp : r • normal T i∈Metric.closedBall (0:Plane) r := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
      normal_norm,mul_one]
  have hm := (mem_region_iff_halfplanes T _).mp (hball hp) i
  rwa [dotp_smul_right,normal_gram,if_pos rfl,mul_one] at hm

theorem actual_inradius_bound (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) : r≤Real.sqrt 3/6 := by
  have hs := offset_sum T
  linarith [offset_ge_radius T hr hball 0,offset_ge_radius T hr hball 1,
    offset_ge_radius T hr hball 2]

/-- Two unit normals at 120 degrees recover the squared norm exactly. -/
theorem norm_from_two_supports {n m p : Plane} {a b : ℝ}
    (hn : dotp n n=1) (hm : dotp m m=1) (hnm : dotp n m=-1/2)
    (ha : dotp n p=a) (hb : dotp m p=b) : ‖p‖^2=4/3*(a^2+a*b+b^2) := by
  have hmn : dotp m n=-1/2 := by rw [dotp_comm]; exact hnm
  have hp : p=((4*a+2*b)/3) • n+((2*a+4*b)/3) • m := by
    apply eq_of_two_dot_eq hn hm hnm
    · rw [ha,dotp_add_right,dotp_smul_right,dotp_smul_right,hn,hnm]; ring
    · rw [hb,dotp_add_right,dotp_smul_right,dotp_smul_right,hmn,hm]; ring
  rw [hp,CommonReach.norm_combination_sq,CommonReach.norm_sq,CommonReach.norm_sq,hn,hm,hnm]
  ring

theorem support_pair_bound {a b r : ℝ} (hr : 0≤r) (ha : r≤a) (hb : r≤b)
    (hs : a+b≤NICertificate.halfRoot-r) : 4/3*(a^2+a*b+b^2)≤boundSq r := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  have hS : 0≤NICertificate.halfRoot+a+b-2*r := by linarith
  have hq := mul_nonneg (sub_nonneg.mpr hs) hS
  have hh2 := ExtremeTriangle.halfRoot_sq
  dsimp [boundSq]
  dsimp [NICertificate.halfRoot] at hh2 hq
  nlinarith

theorem actual_vertex_bound (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) (i : Fin 3) :
    ‖T.vertex i‖^2≤boundSq r := by
  have hoff := offset_ge_radius T hr hball
  have hs : offset T 0+offset T 1+offset T 2=NICertificate.halfRoot := offset_sum T
  have hp (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
      (hbudget : offset T j+offset T k≤NICertificate.halfRoot-r) :
      ‖T.vertex i‖^2≤boundSq r := by
    have hj : dotp (normal T j) (T.vertex i)=offset T j := by
      rw [normal_vertex_dot,if_neg (Ne.symm hij)]; ring
    have hk : dotp (normal T k) (T.vertex i)=offset T k := by
      rw [normal_vertex_dot,if_neg (Ne.symm hik)]; ring
    rw [norm_from_two_supports (by simpa using normal_gram T j j)
      (by simpa using normal_gram T k k) (by simpa [hjk] using normal_gram T j k) hj hk]
    exact support_pair_bound hr (hoff j) (hoff k) hbudget
  fin_cases i
  · exact hp 0 1 2 (by decide) (by decide) (by decide) (by linarith [hoff 0])
  · exact hp 1 2 0 (by decide) (by decide) (by decide) (by linarith [hoff 1])
  · exact hp 2 0 1 (by decide) (by decide) (by decide) (by linarith [hoff 2])

/-- The disk bound controls all points of the same actual closed triangle. -/
theorem actual_triangle_ball (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) :
    T.region⊆Metric.closedBall (0:Plane) (Real.sqrt (boundSq r)) := by
  apply convexHull_min
  · rintro _ ⟨i,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (boundSq_pos r).le]
    exact actual_vertex_bound T hr hball i
  · exact convex_closedBall _ _

theorem actual_triangle_bound (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) {p : Plane} (hp : p∈T.region) :
    ‖p‖^2≤boundSq r := by
  have hm := actual_triangle_ball T hr hball hp
  rw [Metric.mem_closedBall,dist_zero_right] at hm
  have hs := (sq_le_sq₀ (norm_nonneg p) (Real.sqrt_nonneg (boundSq r))).mpr hm
  rwa [Real.sq_sqrt (boundSq_pos r).le] at hs

/-- The smaller algebraic root is forced by the actual inradius bound. -/
theorem radius_le_rmax {r t : ℝ} (hr : r≤Real.sqrt 3/6)
    (hpoint : 1-t+t^2≤boundSq r) : r≤IntruderReach.rmax t := by
  have hs3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hp3 : 0<Real.sqrt (3:ℝ) := by positivity
  have hrad : 0≤3-4*t+4*t^2 := by nlinarith [sq_nonneg (t-1/2)]
  have hs := Real.sq_sqrt hrad
  have hp := Real.sqrt_nonneg (3-4*t+4*t^2)
  have hright : 0≤Real.sqrt 3-4*r := by linarith
  have hroot : Real.sqrt (3-4*t+4*t^2)≤Real.sqrt 3-4*r := by
    apply (sq_le_sq₀ hp hright).mp
    unfold boundSq at hpoint
    nlinarith
  unfold IntruderReach.rmax
  linarith

/-- Any actual central point at least as far as an edge parameter gives the
closed gap-endpoint radius restriction, independently of its orientation. -/
theorem actual_endpoint_radius (T : UnitTriangle) {r t : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) {p : Plane} (hp : p∈T.region)
    (hpoint : 1-t+t^2≤‖p‖^2) : r≤IntruderReach.rmax t :=
  radius_le_rmax (actual_inradius_bound T hr hball)
    (hpoint.trans (actual_triangle_bound T hr hball hp))

/-- A point strictly beyond the hexagon apothem forces the strict gap-small bound. -/
theorem actual_beyond_apothem (T : UnitTriangle) {r : ℝ} (hr : 0≤r)
    (hball : Metric.closedBall (0:Plane) r⊆T.region) {p : Plane} (hp : p∈T.region)
    (hpoint : 3/4<‖p‖^2) : r<IntruderReach.rmax (1/2) := by
  have hi := actual_inradius_bound T hr hball
  have hb := actual_triangle_bound T hr hball hp
  have hs3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp3 : 0<Real.sqrt (3:ℝ) := by positivity
  have hp2 := Real.sqrt_nonneg (2:ℝ)
  have hright : 0≤Real.sqrt 3-4*r := by linarith
  have hroot : Real.sqrt 2<Real.sqrt 3-4*r := by
    apply (sq_lt_sq₀ hp2 hright).mp
    unfold boundSq at hb
    nlinarith
  norm_num [IntruderReach.rmax]
  linarith

theorem rmax_symm (t : ℝ) : IntruderReach.rmax (1-t)=IntruderReach.rmax t := by
  have he : 3-4*(1-t)+4*(1-t)^2=3-4*t+4*t^2 := by ring
  unfold IntruderReach.rmax
  rw [he]

theorem rmax_half_lt_halfRoot : IntruderReach.rmax (1/2)<NICertificate.halfRoot/2 := by
  have hh := ExtremeTriangle.halfRoot_sq
  have hp := ExtremeTriangle.halfRoot_pos
  have hr := IntruderReach.rmax_half_lt_two_twentyfive
  nlinarith

end
end HexagonCover.CentralRadius
