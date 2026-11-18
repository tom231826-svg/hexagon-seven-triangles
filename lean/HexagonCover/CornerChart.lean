import HexagonCover.ExteriorLoss

/-! Selection of a physical corner-normal chart, with one reflection of the
whole plane when necessary. These are coordinate identities, not area formulas. -/

namespace HexagonCover.CornerChart

noncomputable section

open TriangleFrame SupportGeometry ExteriorLoss

def reflect (p : Plane) : Plane := point (p 0) (-p 1)
def maybeReflect (flip : Bool) (p : Plane) : Plane := if flip then reflect p else p

theorem reflect_reflect (p : Plane) : reflect (reflect p) = p := by
  ext i
  fin_cases i <;> simp [reflect]

theorem dot_reflect (p q : Plane) : dotp (reflect p) (reflect q) = dotp p q := by
  simp [reflect, dotp]

def reflectionLinear : Plane →ₗ[ℝ] Plane where
  toFun := reflect
  map_add' p q := by ext i; fin_cases i <;> simp [reflect] <;> ring
  map_smul' a p := by ext i; fin_cases i <;> simp [reflect]

theorem reflection_det : LinearMap.det reflectionLinear = -1 := by
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis reflectionLinear = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, reflectionLinear, reflect]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, hm]
  norm_num [Matrix.det_fin_two]

theorem reflection_area (s : Set Plane) :
    MeasureTheory.volume.real (reflect '' s) = MeasureTheory.volume.real s := by
  have hm := MeasureTheory.Measure.addHaar_image_linearMap
    (MeasureTheory.volume : MeasureTheory.Measure Plane) reflectionLinear s
  rw [reflection_det] at hm
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] at hm
  exact congrArg ENNReal.toReal hm

theorem reflect_vertex (i : Fin 6) : reflect (hexVertex 1 i) = hexVertex 1 (-i) := by
  fin_cases i <;> ext j <;> fin_cases j <;> norm_num [reflect, hexVertex] <;> ring

theorem reflection_hexagon : reflect '' Hexagon 1 = Hexagon 1 := by
  have hr : reflect '' Set.range (hexVertex 1) = Set.range (hexVertex 1) := by
    ext p
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨-i, (reflect_vertex i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨hexVertex 1 (-i), ⟨-i, rfl⟩, ?_⟩
      simpa using reflect_vertex (-i)
  have h := reflectionLinear.image_convexHull (Set.range (hexVertex 1))
  change reflect '' Hexagon 1 = convexHull ℝ (reflect '' Set.range (hexVertex 1)) at h
  rw [hr] at h
  exact h

/-- Reflecting the whole region preserves its actual exterior area, including
all protrusions and boundary points. -/
theorem reflection_exterior_area (s : Set Plane) :
    MeasureTheory.volume.real ((reflect '' s) \ Hexagon 1) =
      MeasureTheory.volume.real (s \ Hexagon 1) := by
  have hinj : Function.Injective reflect := Function.LeftInverse.injective reflect_reflect
  have he := Set.image_sdiff hinj s (Hexagon 1)
  rw [reflection_hexagon] at he
  rw [← he, reflection_area]

theorem reflection_dist (p q : Plane) : dist (reflect p) (reflect q) = dist p q := by
  have h1 := dist_point_sq (p 0) (-p 1) (q 0) (-q 1)
  have h2 := dist_sq_coordinates p q
  change dist (reflect p) (reflect q) ^ 2 = _ at h1
  nlinarith [dist_nonneg (x := reflect p) (y := reflect q), dist_nonneg (x := p) (y := q)]

/-- The reflected triangle is constructed from the same three actual vertices. -/
def reflectedTriangle (T : UnitTriangle) : UnitTriangle where
  vertex i := reflect (T.vertex i)
  edgeLength i j hij := by rw [reflection_dist]; exact T.edgeLength i j hij

theorem reflectedTriangle_region (T : UnitTriangle) :
    (reflectedTriangle T).region = reflect '' T.region := by
  have h := reflectionLinear.image_convexHull (Set.range T.vertex)
  change reflect '' T.region = convexHull ℝ (reflect '' Set.range T.vertex) at h
  rw [← Set.range_comp] at h
  exact h.symm

theorem reflection_corner : reflect corner = corner := by
  ext i
  fin_cases i <;> simp [reflect, corner]

theorem reflection_upperEndpoint (a : ℝ) : reflect (upperEndpoint a) = lowerEndpoint a := by
  ext i
  fin_cases i <;> simp [reflect, upperEndpoint, lowerEndpoint, corner, upperRay, lowerRay]

theorem reflection_lowerEndpoint (b : ℝ) : reflect (lowerEndpoint b) = upperEndpoint b := by
  have h := congrArg reflect (reflection_upperEndpoint b)
  simpa only [reflect_reflect] using h.symm

theorem reflectedTriangle_ball (T : UnitTriangle) {r : ℝ}
    (hball : Metric.ball corner r ⊆ T.region) :
    Metric.ball corner r ⊆ (reflectedTriangle T).region := by
  intro p hp
  have hp' : reflect p ∈ Metric.ball corner r := by
    rw [Metric.mem_ball, ← reflection_corner, reflection_dist]
    exact hp
  rw [reflectedTriangle_region]
  exact ⟨reflect p, hball hp', reflect_reflect p⟩

theorem reflectedTriangle_exterior_area (T : UnitTriangle) :
    MeasureTheory.volume.real ((reflectedTriangle T).region \ Hexagon 1) =
      MeasureTheory.volume.real (T.region \ Hexagon 1) := by
  rw [reflectedTriangle_region, reflection_exterior_area]

theorem nvec_cyclic (c d : ℝ) (k i : Fin 3) :
    nvec ((nvec c d k) 0) ((nvec c d k) 1) i = nvec c d (k + i) := by
  fin_cases k <;> fin_cases i <;> ext j <;> fin_cases j
  all_goals simp [nvec, NICertificate.normalValues]
  all_goals ring_nf
  all_goals rw [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem nvec_reflect (c d : ℝ) (i : Fin 3) :
    nvec c (-d) i = reflect (nvec c d (inverseRole i)) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [nvec, NICertificate.normalValues, reflect, inverseRole] <;> ring

theorem inverseRole_involutive (i : Fin 3) : inverseRole (inverseRole i) = i := by
  fin_cases i <;> rfl

theorem exists_right_normal {c d : ℝ} (hc : 0 ≤ c) (hu : c ^ 2 + d ^ 2 = 1) :
    ∃ k : Fin 3, (1 / 2 : ℝ) ≤ (nvec c d k) 0 := by
  by_cases hbig : 1 / 2 ≤ c
  · exact ⟨0, hbig⟩
  have hcsmall : c < 1 / 2 := lt_of_not_ge hbig
  have hh := ExtremeTriangle.halfRoot_pos
  have hhsq := ExtremeTriangle.halfRoot_sq
  have hprod : 0 ≤ (1 - 2 * c) * (1 + c) :=
    mul_nonneg (by linarith) (by linarith)
  have hsquare : (NICertificate.halfRoot * d) ^ 2 = (3 / 4) * (1 - c ^ 2) := by
    rw [mul_pow, hhsq]
    nlinarith [hu]
  by_cases hd : 0 ≤ d
  · refine ⟨2, ?_⟩
    change 1 / 2 ≤ -1 / 2 * c + NICertificate.halfRoot * d
    nlinarith [mul_nonneg hh.le hd]
  · refine ⟨1, ?_⟩
    change 1 / 2 ≤ -1 / 2 * c - NICertificate.halfRoot * d
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh.le (le_of_lt (lt_of_not_ge hd))]

theorem exists_right_frame (T : UnitTriangle) :
    ∃ c d : ℝ, ∃ b : Fin 3 → ℝ,
      1 / 2 ≤ c ∧ c ^ 2 + d ^ 2 = 1 ∧
      b 0 + b 1 + b 2 = NICertificate.halfRoot ∧
      ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ b i := by
  obtain ⟨c, d, b, hc, hu, hsum, hmem⟩ := exists_normal_frame T
  obtain ⟨k, hk⟩ := exists_right_normal hc hu
  refine ⟨(nvec c d k) 0, (nvec c d k) 1, fun i => b (k + i), hk, ?_, ?_, ?_⟩
  · have hg := nvec_gram hu k k
    simp only [ite_true] at hg
    change (nvec c d k) 0 * (nvec c d k) 0 +
      (nvec c d k) 1 * (nvec c d k) 1 = 1 at hg
    nlinarith
  · fin_cases k <;> norm_num <;> linarith
  · intro p
    rw [hmem]
    change (∀ i, dotp (nvec c d i) p ≤ b i) ↔ _
    simp_rw [nvec_cyclic]
    constructor
    · intro hp i
      exact hp (k + i)
    · intro hp i
      simpa using hp (i - k)

/-- After cyclic relabelling and, if needed, one reflection of the whole plane,
an actual triangle has a unit base normal with nonnegative coordinates and
x-coordinate at least one half. -/
theorem exists_corner_frame (T : UnitTriangle) :
    ∃ flip : Bool, ∃ c d : ℝ, ∃ b : Fin 3 → ℝ,
      1 / 2 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧
      b 0 + b 1 + b 2 = NICertificate.halfRoot ∧
      ∀ p : Plane, p ∈ T.region ↔
        ∀ i, dotp (nvec c d i) (maybeReflect flip p) ≤ b i := by
  obtain ⟨c, d, b, hc, hu, hsum, hmem⟩ := exists_right_frame T
  by_cases hd : 0 ≤ d
  · exact ⟨false, c, d, b, hc, hd, hu, hsum, hmem⟩
  · refine ⟨true, c, -d, fun i => b (inverseRole i), hc, by linarith,
      by nlinarith, ?_, ?_⟩
    · simp only [inverseRole]
      norm_num
      linarith
    · intro p
      rw [hmem]
      change (∀ i, dotp (nvec c d i) p ≤ b i) ↔
        ∀ i, dotp (nvec c (-d) i) (reflect p) ≤ b (inverseRole i)
      simp_rw [nvec_reflect, dot_reflect]
      constructor
      · intro hp i
        exact hp (inverseRole i)
      · intro hp i
        simpa only [inverseRole_involutive] using hp (inverseRole i)

def parameter (c d : ℝ) : ℝ := -1 / 2 + NICertificate.halfRoot * d / c
def Q (x : ℝ) : ℝ := 1 + x + x ^ 2

theorem Q_pos (x : ℝ) : 0 < Q x := by
  unfold Q
  nlinarith [sq_nonneg (x + 1 / 2)]

theorem parameter_bounds {c d : ℝ} (hc : 1 / 2 ≤ c) (hd : 0 ≤ d)
    (hu : c ^ 2 + d ^ 2 = 1) : -1 / 2 ≤ parameter c d ∧ parameter c d ≤ 1 := by
  have hcpos : 0 < c := by linarith
  have hh := ExtremeTriangle.halfRoot_pos
  have hhsq := ExtremeTriangle.halfRoot_sq
  have hcsq : 1 / 4 ≤ c ^ 2 := by nlinarith [sq_nonneg (c - 1 / 2)]
  have hdsq : (NICertificate.halfRoot * d) ^ 2 = (3 / 4) * d ^ 2 := by
    rw [mul_pow, hhsq]
  have hmul : NICertificate.halfRoot * d ≤ 3 / 2 * c := by
    nlinarith [mul_nonneg hh.le hd]
  constructor
  · unfold parameter
    have hn := div_nonneg (mul_nonneg hh.le hd) hcpos.le
    linarith
  · unfold parameter
    have hdiv := (div_le_iff₀ hcpos).mpr hmul
    linarith

theorem parameter_identity {c d : ℝ} (hc : 0 < c) (hu : c ^ 2 + d ^ 2 = 1) :
    c ^ 2 * Q (parameter c d) = 3 / 4 := by
  calc
    c ^ 2 * Q (parameter c d) = (3 / 4) * (c ^ 2 + d ^ 2) := by
      unfold Q parameter
      field_simp [ne_of_gt hc]
      ring_nf
      rw [ExtremeTriangle.halfRoot_sq]
      ring
    _ = 3 / 4 := by rw [hu]; ring

theorem upper_coefficients {c d : ℝ} (hc : c ≠ 0) (i : Fin 3) :
    dotp (nvec c d i) upperRay = c * ![parameter c d, 1, -(1 + parameter c d)] i := by
  fin_cases i
  all_goals simp [dotp, nvec, NICertificate.normalValues, upperRay, parameter]
  all_goals field_simp [hc]
  all_goals ring_nf
  all_goals rw [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem lower_coefficients {c d : ℝ} (hc : c ≠ 0) (i : Fin 3) :
    dotp (nvec c d i) lowerRay = c * ![-(1 + parameter c d), parameter c d, 1] i := by
  fin_cases i
  all_goals simp [dotp, nvec, NICertificate.normalValues, lowerRay, parameter]
  all_goals field_simp [hc]
  all_goals ring_nf
  all_goals rw [ExtremeTriangle.halfRoot_sq]
  all_goals ring

/-- These are scalar expressions from the proposed polygon computation. No
theorem here equates them to the measure of a geometric region. -/
def negativeNumerator (x a b : ℝ) : ℝ := -x * a ^ 2 + (1 + x) * b ^ 2
def positiveNumerator (x a b : ℝ) : ℝ :=
  x * (1 + x) * a ^ 2 + 2 * x * a * b + (1 + x) * b ^ 2

theorem negative_min_bound {x a b : ℝ} (hx : -1 / 2 ≤ x) (hx0 : x ≤ 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Q x * (min a b) ^ 2 ≤ negativeNumerator x a b := by
  have hm : 0 ≤ min a b := le_min ha hb
  have hma : (min a b) ^ 2 ≤ a ^ 2 := by nlinarith [min_le_left a b]
  have hmb : (min a b) ^ 2 ≤ b ^ 2 := by nlinarith [min_le_right a b]
  have h1 := mul_nonneg (neg_nonneg.mpr hx0) (sub_nonneg.mpr hma)
  have h2 := mul_nonneg (show 0 ≤ 1 + x by linarith) (sub_nonneg.mpr hmb)
  have h3 := mul_nonneg (mul_nonneg (neg_nonneg.mpr hx0)
    (show 0 ≤ 1 + x by linarith)) (sq_nonneg (min a b))
  unfold Q negativeNumerator
  nlinarith

theorem positive_min_bound {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Q x * (min a b) ^ 2 ≤ positiveNumerator x a b := by
  have hm : 0 ≤ min a b := le_min ha hb
  have hma : (min a b) ^ 2 ≤ a ^ 2 := by nlinarith [min_le_left a b]
  have hmb : (min a b) ^ 2 ≤ b ^ 2 := by nlinarith [min_le_right a b]
  have h1 := mul_nonneg (mul_nonneg hx (show 0 ≤ 1 + x by linarith))
    (sub_nonneg.mpr hma)
  have h2 := mul_nonneg (show 0 ≤ 1 + x by linarith) (sub_nonneg.mpr hmb)
  have h3 := mul_nonneg hx (sq_nonneg (min a b))
  have h4 := mul_nonneg (mul_nonneg hx ha) hb
  unfold Q positiveNumerator
  nlinarith

theorem negative_chart_sum_lt_one {x a b : ℝ} (hx : -1 / 2 ≤ x) (hx0 : x ≤ 0)
    (hstrict : (a + b) ^ 2 < Q x) : a + b < 1 := by
  have hprod := mul_nonpos_of_nonpos_of_nonneg hx0 (show 0 ≤ 1 + x by linarith)
  unfold Q at hstrict
  nlinarith [sq_nonneg (a + b - 1)]

def supportSum (x a b : ℝ) : ℝ := a * x + max a (b * x) + b

theorem positive_max_bound {x a b : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : 1 ≤ a + b) (hfeas : (supportSum x a b) ^ 2 ≤ Q x) :
    Q x * (max a b) ^ 2 ≤ positiveNumerator x a b := by
  by_cases haborder : b ≤ a
  · rw [max_eq_left haborder]
    have hbx : b * x ≤ a := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hx1)]
    rw [supportSum, max_eq_left hbx] at hfeas
    have hS : 1 + x * a ≤ a * x + a + b := by linarith
    have hS0 : 0 ≤ 1 + x * a := by positivity
    have hsquare : (1 + x * a) ^ 2 ≤ (a * x + a + b) ^ 2 := by nlinarith
    have hK : 0 ≤ 1 + x - 2 * a - x * a ^ 2 := by
      unfold Q at hfeas
      have hm : 0 ≤ x * (1 + x - 2 * a - x * a ^ 2) := by nlinarith
      exact nonneg_of_mul_nonneg_right hm hx
    have hdiff : 0 ≤ (a + b - 1) *
        (2 * x * a + (1 + x) * (b + 1 - a)) := by
      apply mul_nonneg (by linarith)
      exact add_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
    unfold Q positiveNumerator
    nlinarith
  · have haborder' : a ≤ b := le_of_lt (lt_of_not_ge haborder)
    rw [max_eq_right haborder']
    by_cases hbx : b * x ≤ a
    · have hprod := mul_nonneg (sub_nonneg.mpr hbx) hb
      have hsq := mul_nonneg (show 0 ≤ 1 + x by linarith) (sq_nonneg a)
      have hnonneg : 0 ≤ (1 + x) * a ^ 2 + 2 * a * b - x * b ^ 2 := by
        nlinarith [mul_nonneg hx.le (sq_nonneg b)]
      have hm := mul_nonneg hx.le hnonneg
      unfold Q positiveNumerator
      nlinarith
    · rw [supportSum, max_eq_right (le_of_lt (lt_of_not_ge hbx))] at hfeas
      have hS : x + b ≤ a * x + b * x + b := by nlinarith
      have hS0 : 0 ≤ x + b := by linarith
      have hsquare : (x + b) ^ 2 ≤ (a * x + b * x + b) ^ 2 := by nlinarith
      have hK : 0 ≤ 1 + x - 2 * x * b - b ^ 2 := by
        unfold Q at hfeas
        nlinarith
      have hdiff : 0 ≤ (a + b - 1) * ((1 + x) * (a + 1 - b) + 2 * b) := by
        apply mul_nonneg (by linarith)
        exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      have hnonneg : 0 ≤ (1 + x) * a ^ 2 + 2 * a * b - x * b ^ 2 := by
        nlinarith
      have hm := mul_nonneg hx.le hnonneg
      unfold Q positiveNumerator
      nlinarith

end
end HexagonCover.CornerChart
