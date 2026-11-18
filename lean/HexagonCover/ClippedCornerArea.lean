import HexagonCover.CornerChart
import HexagonCover.TriangleMeasure

/-! Constructive exterior-area estimates from two actual triangular subregions.
This proof is source-exposed, but does not assume a polygon clipping formula:
each subregion is proved contained in the same actual triangle and exterior
modulo a null line, and its Lebesgue area is measured by a determinant. -/

namespace HexagonCover.ClippedCornerArea

noncomputable section

open MeasureTheory MeasureTheory.Measure TriangleMeasure TriangleFrame
  SupportGeometry ExteriorLoss CornerChart

def delta : ℝ := Real.sqrt 3 / 4

def conePoint (P M : ℝ) : Plane :=
  point ((P + M) / 2) (NICertificate.halfRoot * (P - M))

def plusForm : Plane →ₗ[ℝ] ℝ where
  toFun p := p 0 + p 1 / Real.sqrt 3
  map_add' p q := by simp; ring
  map_smul' a p := by simp; ring

def minusForm : Plane →ₗ[ℝ] ℝ where
  toFun p := p 0 - p 1 / Real.sqrt 3
  map_add' p q := by simp; ring
  map_smul' a p := by simp; ring

@[simp] theorem plus_conePoint (P M : ℝ) : plusForm (conePoint P M) = P := by
  simp [plusForm, conePoint, NICertificate.halfRoot]
  field_simp [StandardCover.sqrt3_ne_zero]
  ring

@[simp] theorem minus_conePoint (P M : ℝ) : minusForm (conePoint P M) = M := by
  simp [minusForm, conePoint, NICertificate.halfRoot]
  field_simp [StandardCover.sqrt3_ne_zero]
  ring

theorem upperRay_conePoint (a : ℝ) : a • upperRay = conePoint 0 (-a) := by
  ext i
  fin_cases i <;> simp [upperRay, conePoint] <;> ring

theorem lowerRay_conePoint (b : ℝ) : b • lowerRay = conePoint (-b) 0 := by
  ext i
  fin_cases i <;> simp [lowerRay, conePoint] <;> ring

theorem det_conePoint (P M R S : ℝ) :
    det (conePoint P M) (conePoint R S) = NICertificate.halfRoot * (M * R - P * S) := by
  simp [det, conePoint]
  ring

theorem chart_dot {c d : ℝ} (hc : c ≠ 0) (P M : ℝ) (i : Fin 3) :
    dotp (nvec c d i) (conePoint P M) = c *
      ![(1 + parameter c d) * P - parameter c d * M,
        -parameter c d * P - M, -P + (1 + parameter c d) * M] i := by
  fin_cases i
  all_goals simp [dotp, nvec, NICertificate.normalValues, conePoint, parameter]
  all_goals field_simp [hc]
  all_goals ring_nf
  all_goals rw [ExtremeTriangle.halfRoot_sq]
  all_goals ring

theorem plus_corner : plusForm corner = 1 := by simp [plusForm, corner]
theorem minus_corner : minusForm corner = 1 := by simp [minusForm, corner]

theorem plusForm_ne_zero : plusForm ≠ 0 := by
  intro h
  have he := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f corner) h
  rw [plus_corner] at he
  norm_num at he

theorem minusForm_ne_zero : minusForm ≠ 0 := by
  intro h
  have he := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f corner) h
  rw [minus_corner] at he
  norm_num at he

def shifted (f : Plane →ₗ[ℝ] ℝ) : Plane →ᵃ[ℝ] ℝ where
  toFun p := f (p - corner)
  linear := f
  map_vadd' p v := by simp [map_add, map_sub]; ring

theorem shifted_line_null (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    volume {p : Plane | f (p - corner) = 0} = 0 := by
  have hk : f.ker ≠ ⊤ := fun h => hf (LinearMap.ker_eq_top.mp h)
  have hn := addHaar_submodule (volume : Measure Plane) f.ker hk
  have he : {p : Plane | f (p - corner) = 0} =
      (fun z => corner + z) '' (f.ker : Set Plane) := by
    ext p
    constructor
    · intro hp
      exact ⟨p - corner, hp, by abel_nf⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  rw [he, Set.image_add_left, measure_preimage_add]
  exact hn

theorem triangle_nonneg (f : Plane →ₗ[ℝ] ℝ) {p q r : Plane}
    (hp : 0 ≤ f (p - corner)) (hq : 0 ≤ f (q - corner)) (hr : 0 ≤ f (r - corner)) :
    triangle p q r ⊆ {z | 0 ≤ f (z - corner)} :=
  triangle_subset_of_convex ((convex_Ici (0 : ℝ)).affine_preimage (shifted f)) hp hq hr

theorem triangle_nonpos (f : Plane →ₗ[ℝ] ℝ) {p q r : Plane}
    (hp : f (p - corner) ≤ 0) (hq : f (q - corner) ≤ 0) (hr : f (r - corner) ≤ 0) :
    triangle p q r ⊆ {z | f (z - corner) ≤ 0} :=
  triangle_subset_of_convex ((convex_Iic (0 : ℝ)).affine_preimage (shifted f)) hp hq hr

theorem hexagon_forms {p : Plane} (hp : p ∈ Hexagon 1) :
    plusForm (p - corner) ≤ 0 ∧ minusForm (p - corner) ≤ 0 := by
  have hh := hexagon_subset_cornerCone hp
  rw [map_sub, map_sub, plus_corner, minus_corner]
  change p 0 + p 1 / Real.sqrt 3 ≤ 1 ∧ p 0 - p 1 / Real.sqrt 3 ≤ 1 at hh
  change p 0 + p 1 / Real.sqrt 3 - 1 ≤ 0 ∧ p 0 - p 1 / Real.sqrt 3 - 1 ≤ 0
  constructor <;> linarith [hh.1, hh.2]

theorem two_subregions_bound (T : UnitTriangle) (s t : Set Plane)
    (hs : IsCompact s) (ht : IsCompact t) (hsT : s ⊆ T.region) (htT : t ⊆ T.region)
    (hsH : volume (s ∩ Hexagon 1) = 0) (htH : volume (t ∩ Hexagon 1) = 0)
    (hdisj : AEDisjoint volume s t) :
    volume.real s + volume.real t ≤ volume.real (T.region \ Hexagon 1) := by
  have harea := measureReal_union₀ ht.isClosed.measurableSet.nullMeasurableSet hdisj
    hs.measure_ne_top ht.measure_ne_top
  have hnull : volume ((s ∪ t) ∩ Hexagon 1) = 0 := by
    rw [Set.union_inter_distrib_right]
    exact measure_union_null hsH htH
  have hreal : volume.real ((s ∪ t) ∩ Hexagon 1) = 0 := by
    simp only [Measure.real, hnull, ENNReal.toReal_zero]
  have hdecomp := measureReal_inter_add_sdiff (μ := volume)
    (s := s ∪ t) (compact_hexagon 1).isClosed.measurableSet (hs.union ht).measure_ne_top
  have hmono : volume.real ((s ∪ t) \ Hexagon 1) ≤ volume.real (T.region \ Hexagon 1) := by
    refine measureReal_mono
      (Set.sdiff_subset_sdiff_left (Set.union_subset hsT htT)) ?_
    exact measure_ne_top_of_subset Set.sdiff_subset T.compact_region.measure_ne_top
  linarith

/-- A measured lower bound from two actual triangles, exterior except on null
supporting lines and separated except on another null line. -/
theorem two_triangles_bound (T : UnitTriangle) (A V W B : Plane)
    (hO : corner ∈ T.region) (hA : A ∈ T.region) (hV : V ∈ T.region)
    (hW : W ∈ T.region) (hB : B ∈ T.region)
    (hAp : 0 ≤ plusForm (A - corner)) (hVp : 0 ≤ plusForm (V - corner))
    (hWm : 0 ≤ minusForm (W - corner)) (hBm : 0 ≤ minusForm (B - corner))
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (hfA : 0 ≤ f (A - corner)) (hfV : 0 ≤ f (V - corner))
    (hfW : f (W - corner) ≤ 0) (hfB : f (B - corner) ≤ 0) :
    volume.real (triangle corner A V) + volume.real (triangle corner W B) ≤
      volume.real (T.region \ Hexagon 1) := by
  have hp := triangle_nonneg plusForm (p := corner) (by simp) hAp hVp
  have hm := triangle_nonneg minusForm (p := corner) (by simp) hWm hBm
  have hfpos := triangle_nonneg f (p := corner) (by simp) hfA hfV
  have hfneg := triangle_nonpos f (p := corner) (by simp) hfW hfB
  apply two_subregions_bound T _ _ (triangle_compact _ _ _) (triangle_compact _ _ _)
    (triangle_subset_of_convex T.convex_region hO hA hV)
    (triangle_subset_of_convex T.convex_region hO hW hB)
  · apply measure_mono_null _ (shifted_line_null plusForm plusForm_ne_zero)
    intro p h
    exact le_antisymm (hexagon_forms h.2).1 (hp h.1)
  · apply measure_mono_null _ (shifted_line_null minusForm minusForm_ne_zero)
    intro p h
    exact le_antisymm (hexagon_forms h.2).2 (hm h.1)
  · apply measure_mono_null _ (shifted_line_null f hf)
    intro p h
    exact le_antisymm (hfneg h.2) (hfpos h.1)

theorem upper_triangle_area {a P M : ℝ} (ha : 0 ≤ a) (hP : 0 ≤ P) :
    volume.real (triangle corner (upperEndpoint a) (corner + conePoint P M)) = delta * a * P := by
  rw [triangle_area]
  simp only [upperEndpoint, add_sub_cancel_left, upperRay_conePoint, det_conePoint, zero_mul,
    sub_zero, neg_mul]
  rw [abs_of_nonpos (by nlinarith [mul_nonneg (mul_nonneg ExtremeTriangle.halfRoot_pos.le ha) hP])]
  unfold delta NICertificate.halfRoot
  ring

theorem lower_triangle_area {b P M : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) :
    volume.real (triangle corner (corner + conePoint P M) (lowerEndpoint b)) = delta * b * M := by
  rw [triangle_area]
  simp only [lowerEndpoint, add_sub_cancel_left, lowerRay_conePoint, det_conePoint, mul_zero,
    sub_zero, mul_neg]
  rw [abs_of_nonpos (by nlinarith [mul_nonneg (mul_nonneg ExtremeTriangle.halfRoot_pos.le hb) hM])]
  unfold delta NICertificate.halfRoot
  ring

theorem endpoint_support_bounds (T : UnitTriangle) {c d x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : c ≠ 0) (hx : parameter c d = x)
    (hmem : ∀ z : Plane, corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ offs i)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    c * (a * x) ≤ offs 0 ∧ c * a ≤ offs 1 ∧ c * b ≤ offs 2 ∧ c * (b * x) ≤ offs 1 := by
  have hA : ∀ i : Fin 3, a * (c * ![x, 1, -(1 + x)] i) ≤ offs i := by
    intro i
    simpa only [dotp_smul_right, upper_coefficients hc, hx] using (hmem _).mp ha i
  have hB : ∀ i : Fin 3, b * (c * ![-(1 + x), x, 1] i) ≤ offs i := by
    intro i
    simpa only [dotp_smul_right, lower_coefficients hc, hx] using (hmem _).mp hb i
  have hA0 := hA 0
  have hA1 := hA 1
  have hB1 := hB 1
  have hB2 := hB 2
  norm_num at hA0 hA1 hB1 hB2
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

def positiveP (x a b : ℝ) : ℝ := x * (b + (1 + x) * a) / Q x
def positiveM (x a b : ℝ) : ℝ := ((1 + x) * b + x * a) / Q x
def negativeTopP (x a : ℝ) : ℝ := -x * a / Q x
def negativeTopM (x a : ℝ) : ℝ := -(1 + x) * a / Q x
def negativeBottomP (x b : ℝ) : ℝ := x * b / Q x
def negativeBottomM (x b : ℝ) : ℝ := (1 + x) * b / Q x

theorem positive_vertex_forms (x a b : ℝ) :
    (1 + x) * positiveP x a b - x * positiveM x a b = a * x ∧
    -x * positiveP x a b - positiveM x a b = -(a * x + b) ∧
    -positiveP x a b + (1 + x) * positiveM x a b = b := by
  have hq : Q x ≠ 0 := ne_of_gt (Q_pos x)
  dsimp [positiveP, positiveM]
  constructor
  · field_simp [hq]
    unfold Q
    ring
  constructor
  · field_simp [hq]
    unfold Q
    ring
  · field_simp [hq]
    unfold Q
    ring

theorem negative_vertex_forms (x a b : ℝ) :
    (1 + x) * negativeTopP x a - x * negativeTopM x a = 0 ∧
    -x * negativeTopP x a - negativeTopM x a = a ∧
    -negativeTopP x a + (1 + x) * negativeTopM x a = -a ∧
    (1 + x) * negativeBottomP x b - x * negativeBottomM x b = 0 ∧
    -x * negativeBottomP x b - negativeBottomM x b = -b ∧
    -negativeBottomP x b + (1 + x) * negativeBottomM x b = b := by
  have hq : Q x ≠ 0 := ne_of_gt (Q_pos x)
  dsimp [negativeTopP, negativeTopM, negativeBottomP, negativeBottomM]
  repeat' constructor
  all_goals field_simp [hq]
  all_goals unfold Q
  all_goals ring

theorem positive_vertex_mem (T : UnitTriangle) {c d x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 ≤ x) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hparam : parameter c d = x)
    (hmem : ∀ z : Plane, corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ offs i)
    (hpos : ∀ i, 0 ≤ offs i)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    corner + conePoint (positiveP x a b) (positiveM x a b) ∈ T.region := by
  obtain ⟨h0, _, h2, _⟩ := endpoint_support_bounds T (ne_of_gt hc) hparam hmem ha hb
  obtain ⟨hv0, hv1, hv2⟩ := positive_vertex_forms x a b
  apply (hmem _).mpr
  intro i
  rw [chart_dot (ne_of_gt hc), hparam]
  fin_cases i
  · change c * ((1 + x) * positiveP x a b - x * positiveM x a b) ≤ offs 0
    rw [hv0]
    exact h0
  · change c * (-x * positiveP x a b - positiveM x a b) ≤ offs 1
    rw [hv1]
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hc.le (by nlinarith)) (hpos 1)
  · change c * (-positiveP x a b + (1 + x) * positiveM x a b) ≤ offs 2
    rw [hv2]
    exact h2

theorem negative_vertices_mem (T : UnitTriangle) {c d x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hparam : parameter c d = x)
    (hmem : ∀ z : Plane, corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ offs i)
    (hpos : ∀ i, 0 ≤ offs i)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    corner + conePoint (negativeTopP x a) (negativeTopM x a) ∈ T.region ∧
    corner + conePoint (negativeBottomP x b) (negativeBottomM x b) ∈ T.region := by
  obtain ⟨_, h1, h2, _⟩ := endpoint_support_bounds T (ne_of_gt hc) hparam hmem ha hb
  obtain ⟨ht0, ht1, ht2, hb0', hb1', hb2'⟩ := negative_vertex_forms x a b
  constructor
  · apply (hmem _).mpr
    intro i
    rw [chart_dot (ne_of_gt hc), hparam]
    fin_cases i
    · change c * ((1 + x) * negativeTopP x a - x * negativeTopM x a) ≤ offs 0
      rw [ht0, mul_zero]
      exact hpos 0
    · change c * (-x * negativeTopP x a - negativeTopM x a) ≤ offs 1
      rw [ht1]
      exact h1
    · change c * (-negativeTopP x a + (1 + x) * negativeTopM x a) ≤ offs 2
      rw [ht2]
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)) (hpos 2)
  · apply (hmem _).mpr
    intro i
    rw [chart_dot (ne_of_gt hc), hparam]
    fin_cases i
    · change c * ((1 + x) * negativeBottomP x b - x * negativeBottomM x b) ≤ offs 0
      rw [hb0', mul_zero]
      exact hpos 0
    · change c * (-x * negativeBottomP x b - negativeBottomM x b) ≤ offs 1
      rw [hb1']
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)) (hpos 1)
    · change c * (-negativeBottomP x b + (1 + x) * negativeBottomM x b) ≤ offs 2
      rw [hb2']
      exact h2

def separator (P M : ℝ) : Plane →ₗ[ℝ] ℝ := M • plusForm - P • minusForm

@[simp] theorem separator_conePoint (P M R S : ℝ) :
    separator P M (conePoint R S) = M * R - P * S := by simp [separator]

theorem separator_ne_zero {P M : ℝ} (hM : M ≠ 0) : separator P M ≠ 0 := by
  intro he
  have h := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (conePoint 1 0)) he
  simp only [separator_conePoint, mul_one, mul_zero, sub_zero, LinearMap.zero_apply] at h
  exact hM h

theorem cone_subtriangles_bound (T : UnitTriangle) {a b P₁ M₁ P₂ M₂ R S : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hP : 0 ≤ P₁) (hM : 0 ≤ M₂)
    (hS : S ≠ 0) (hRA : 0 ≤ R * a) (hSV : 0 ≤ S * P₁ - R * M₁)
    (hSW : S * P₂ - R * M₂ ≤ 0) (hSB : -S * b ≤ 0)
    (hO : corner ∈ T.region) (hA : upperEndpoint a ∈ T.region)
    (hV : corner + conePoint P₁ M₁ ∈ T.region)
    (hW : corner + conePoint P₂ M₂ ∈ T.region) (hB : lowerEndpoint b ∈ T.region) :
    delta * a * P₁ + delta * b * M₂ ≤ volume.real (T.region \ Hexagon 1) := by
  have hAp : 0 ≤ plusForm (upperEndpoint a - corner) := by
    simp [upperEndpoint, upperRay_conePoint]
  have hBm : 0 ≤ minusForm (lowerEndpoint b - corner) := by
    simp [lowerEndpoint, lowerRay_conePoint]
  have hAf : 0 ≤ separator R S (upperEndpoint a - corner) := by
    simpa [upperEndpoint, upperRay_conePoint] using hRA
  have hBf : separator R S (lowerEndpoint b - corner) ≤ 0 := by
    simpa [lowerEndpoint, lowerRay_conePoint] using hSB
  have hvp : 0 ≤ plusForm (corner + conePoint P₁ M₁ - corner) := by simpa using hP
  have hwm : 0 ≤ minusForm (corner + conePoint P₂ M₂ - corner) := by simpa using hM
  have hvf : 0 ≤ separator R S (corner + conePoint P₁ M₁ - corner) := by simpa using hSV
  have hwf : separator R S (corner + conePoint P₂ M₂ - corner) ≤ 0 := by simpa using hSW
  have h := two_triangles_bound T (upperEndpoint a) (corner + conePoint P₁ M₁)
    (corner + conePoint P₂ M₂) (lowerEndpoint b) hO hA hV hW hB hAp hvp hwm hBm
    (separator R S) (separator_ne_zero hS) hAf hvf hwf hBf
  rwa [upper_triangle_area ha0 hP, lower_triangle_area hb0 hM] at h

/-- The positive expression is a proved lower bound on actual exterior area,
obtained by measuring two physical subtriangles. No clipping-area premise. -/
theorem positive_area_bound (T : UnitTriangle) {c d x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 ≤ x) (ha0 : 0 ≤ a) (hb0 : 0 < b)
    (hparam : parameter c d = x)
    (hmem : ∀ z : Plane, corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ offs i)
    (hpos : ∀ i, 0 ≤ offs i) (hO : corner ∈ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    delta * positiveNumerator x a b / Q x ≤ volume.real (T.region \ Hexagon 1) := by
  have hP : 0 ≤ positiveP x a b := by
    unfold positiveP
    exact div_nonneg (mul_nonneg hx (by positivity)) (Q_pos x).le
  have hM : 0 < positiveM x a b := by
    unfold positiveM
    exact div_pos (by positivity) (Q_pos x)
  have hv := positive_vertex_mem T hc hx ha0 hb0.le hparam hmem hpos ha hb
  have h := cone_subtriangles_bound T ha0 hb0.le hP hM.le (ne_of_gt hM)
    (mul_nonneg hP ha0) (show 0 ≤ positiveM x a b * positiveP x a b -
      positiveP x a b * positiveM x a b by nlinarith)
    (show positiveM x a b * positiveP x a b - positiveP x a b * positiveM x a b ≤ 0 by nlinarith)
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hM.le) hb0.le) hO ha hv hv hb
  convert h using 1
  unfold positiveP positiveM positiveNumerator
  ring

/-- The nonpositive chart also uses two measured physical subtriangles. -/
theorem negative_area_bound (T : UnitTriangle) {c d x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hxlo : -1 / 2 ≤ x) (hx : x ≤ 0) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hparam : parameter c d = x)
    (hmem : ∀ z : Plane, corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ offs i)
    (hpos : ∀ i, 0 ≤ offs i) (hO : corner ∈ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    delta * negativeNumerator x a b / Q x ≤ volume.real (T.region \ Hexagon 1) := by
  have htP : 0 ≤ negativeTopP x a := by
    exact div_nonneg (mul_nonneg (neg_nonneg.mpr hx) ha0) (Q_pos x).le
  have hbM : 0 ≤ negativeBottomM x b := by
    exact div_nonneg (mul_nonneg (by linarith) hb0) (Q_pos x).le
  have htdiff : negativeTopP x a - negativeTopM x a = a / Q x := by
    unfold negativeTopP negativeTopM
    ring
  have hbdiff : negativeBottomP x b - negativeBottomM x b = -b / Q x := by
    unfold negativeBottomP negativeBottomM
    ring
  obtain ⟨ht, hb'⟩ := negative_vertices_mem T hc ha0 hb0 hparam hmem hpos ha hb
  have h := cone_subtriangles_bound T ha0 hb0 htP hbM (P₁ := negativeTopP x a)
    (M₁ := negativeTopM x a) (P₂ := negativeBottomP x b) (M₂ := negativeBottomM x b)
    (R := 1) (S := 1) (by norm_num) (by simpa using ha0)
    (by simpa only [one_mul, htdiff] using div_nonneg ha0 (Q_pos x).le)
    (by simpa only [one_mul, hbdiff] using (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb0) (Q_pos x).le))
    (by simpa using neg_nonpos.mpr hb0) hO ha ht hb' hb
  convert h using 1
  unfold negativeTopP negativeBottomM negativeNumerator
  ring

theorem chart_feasibility {c d x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hu : c ^ 2 + d ^ 2 = 1) (hparam : parameter c d = x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : offs 0 + offs 1 + offs 2 = NICertificate.halfRoot)
    (hstrict : 0 < offs 0)
    (h0 : c * (a * x) ≤ offs 0) (h1 : c * a ≤ offs 1)
    (h2 : c * b ≤ offs 2) (h1b : c * (b * x) ≤ offs 1) :
    (a + b) ^ 2 < Q x ∧ (0 ≤ x → (supportSum x a b) ^ 2 ≤ Q x) := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hidentity := parameter_identity hc hu
  rw [hparam] at hidentity
  have hhsq := ExtremeTriangle.halfRoot_sq
  have hsumlt : c * (a + b) < NICertificate.halfRoot := by nlinarith
  have hsquare := (sq_lt_sq₀ (mul_nonneg hc.le (add_nonneg ha hb)) hh.le).mpr hsumlt
  constructor
  · apply (mul_lt_mul_iff_of_pos_left (sq_pos_of_pos hc)).mp
    nlinarith
  · intro hx
    have hS0 : 0 ≤ supportSum x a b := by
      unfold supportSum
      exact add_nonneg (add_nonneg (mul_nonneg ha hx) (le_trans ha (le_max_left _ _))) hb
    have hS : c * supportSum x a b ≤ NICertificate.halfRoot := by
      unfold supportSum
      by_cases hab : b * x ≤ a
      · rw [max_eq_left hab]
        nlinarith
      · rw [max_eq_right (le_of_lt (lt_of_not_ge hab))]
        nlinarith
    have hSq := (sq_le_sq₀ (mul_nonneg hc.le hS0) hh.le).mpr hS
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hc)).mp
    nlinarith

theorem numerator_to_area {x N m L : ℝ} (hN : Q x * m ^ 2 ≤ N)
    (hL : delta * N / Q x ≤ L) : delta * m ^ 2 ≤ L := by
  have hd : 0 ≤ delta := by unfold delta; positivity
  have hq : m ^ 2 ≤ N / Q x := (le_div_iff₀ (Q_pos x)).mpr (by nlinarith)
  calc
    delta * m ^ 2 ≤ delta * (N / Q x) := mul_le_mul_of_nonneg_left hq hd
    _ = delta * N / Q x := by ring
    _ ≤ L := hL

/-- Conditional only on a physical chart for this very triangle; the final
theorem below constructs the chart and eliminates all these chart premises. -/
theorem charted_loss_bounds (T : UnitTriangle) {c d a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1 / 2 ≤ c) (hd : 0 ≤ d) (hu : c ^ 2 + d ^ 2 = 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hsum : offs 0 + offs 1 + offs 2 = NICertificate.halfRoot)
    (hpos : ∀ i, 0 < offs i)
    (hmem : ∀ z : Plane, corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ offs i)
    (hO : corner ∈ T.region) (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    delta * (min a b) ^ 2 ≤ volume.real (T.region \ Hexagon 1) ∧
      (1 ≤ a + b → delta * (max a b) ^ 2 ≤ volume.real (T.region \ Hexagon 1)) := by
  let x := parameter c d
  have hcpos : 0 < c := by linarith
  have hparam : parameter c d = x := rfl
  have hxr : -1 / 2 ≤ x ∧ x ≤ 1 := parameter_bounds hc hd hu
  have hp : ∀ i, 0 ≤ offs i := fun i => (hpos i).le
  obtain ⟨h0, h1, h2, h1b⟩ := endpoint_support_bounds T (ne_of_gt hcpos) hparam hmem ha hb
  have hfeas := chart_feasibility hcpos hu hparam ha0.le hb0.le hsum (hpos 0) h0 h1 h2 h1b
  constructor
  · by_cases hx : x ≤ 0
    · exact numerator_to_area (negative_min_bound hxr.1 hx ha0.le hb0.le)
        (negative_area_bound T hcpos hxr.1 hx ha0.le hb0.le hparam hmem hp hO ha hb)
    · have hx0 : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
      exact numerator_to_area (positive_min_bound hx0 ha0.le hb0.le)
        (positive_area_bound T hcpos hx0 ha0.le hb0 hparam hmem hp hO ha hb)
  · intro hab
    have hx : 0 < x := by
      by_contra hn
      have hlt := negative_chart_sum_lt_one hxr.1 (le_of_not_gt hn) hfeas.1
      linarith
    exact numerator_to_area (positive_max_bound hx hxr.2 ha0.le ha1 hb0.le hb1 hab (hfeas.2 hx.le))
      (positive_area_bound T hcpos hx.le ha0.le hb0 hparam hmem hp hO ha hb)

theorem loss_bounds_from_frame (T : UnitTriangle) {c d a b r : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1 / 2 ≤ c) (hd : 0 ≤ d) (hu : c ^ 2 + d ^ 2 = 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hsum : offs 0 + offs 1 + offs 2 = NICertificate.halfRoot)
    (hmem : ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ offs i)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    delta * (min a b) ^ 2 ≤ volume.real (T.region \ Hexagon 1) ∧
      (1 ≤ a + b → delta * (max a b) ^ 2 ≤ volume.real (T.region \ Hexagon 1)) := by
  have hsum' : translatedSupport c d offs 0 + translatedSupport c d offs 1 +
      translatedSupport c d offs 2 = NICertificate.halfRoot := by
    simpa only [Fin.sum_univ_three] using translated_support_sum (c := c) (d := d) hsum
  exact charted_loss_bounds T hc hd hu ha0 ha1 hb0 hb1 hsum'
    (translated_support_pos T hu hmem hr hball)
    (translated_membership T hmem) (hball (Metric.mem_ball_self hr)) ha hb

theorem reflectedTriangle_mem_iff (T : UnitTriangle) (p : Plane) :
    p ∈ (reflectedTriangle T).region ↔ reflect p ∈ T.region := by
  rw [reflectedTriangle_region]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [reflect_reflect] using hq
  · intro hp
    exact ⟨reflect p, hp, reflect_reflect p⟩

/-- Actual sharp local exterior losses for the original unit triangle. Both
reaches and the positive corner disk belong to that same actual triangle.
No orientation, clipping, area-formula, or nonintrusion premise is assumed. -/
theorem actual_corner_loss_bounds (T : UnitTriangle) {a b r : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    delta * (min a b) ^ 2 ≤ volume.real (T.region \ Hexagon 1) ∧
      (1 ≤ a + b → delta * (max a b) ^ 2 ≤ volume.real (T.region \ Hexagon 1)) := by
  obtain ⟨flip, c, d, offs, hc, hd, hu, hsum, hmem⟩ := exists_corner_frame T
  cases flip
  · exact loss_bounds_from_frame T hc hd hu ha0 ha1 hb0 hb1 hsum hmem hr hball ha hb
  · have hmemR : ∀ p : Plane, p ∈ (reflectedTriangle T).region ↔
        ∀ i, dotp (nvec c d i) p ≤ offs i := by
      intro p
      rw [reflectedTriangle_mem_iff, hmem]
      simp only [maybeReflect, Bool.true_eq, ite_true, reflect_reflect]
    have hA : upperEndpoint b ∈ (reflectedTriangle T).region := by
      rw [reflectedTriangle_region]
      exact ⟨lowerEndpoint b, hb, reflection_lowerEndpoint b⟩
    have hB : lowerEndpoint a ∈ (reflectedTriangle T).region := by
      rw [reflectedTriangle_region]
      exact ⟨upperEndpoint a, ha, reflection_upperEndpoint a⟩
    have hR := loss_bounds_from_frame (reflectedTriangle T) hc hd hu hb0 hb1 ha0 ha1 hsum hmemR
      hr (reflectedTriangle_ball T hball) hA hB
    constructor
    · simpa only [min_comm b a, reflectedTriangle_exterior_area] using hR.1
    · intro hab
      simpa only [max_comm b a, reflectedTriangle_exterior_area] using hR.2 (by linarith)

end
end HexagonCover.ClippedCornerArea
