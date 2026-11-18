import HexagonCover.Geometry
import HexagonCover.ExtremeTriangle

/-!
# Actual unit triangles in the normal-coordinate chart

This module constructs support halfplanes from the actual three vertices. The
frame is derived from the equilateral edge equations, rather than assumed as an
extra hypothesis on a covering triangle.
-/

namespace HexagonCover
namespace TriangleFrame

noncomputable section

abbrev dotp (p q : Plane) : ℝ := p 0 * q 0 + p 1 * q 1

theorem dotp_comm (p q : Plane) : dotp p q = dotp q p := by
  unfold dotp
  ring

theorem dotp_add_right (p q r : Plane) : dotp p (q + r) = dotp p q + dotp p r := by
  simp only [dotp, PiLp.add_apply]
  ring

theorem dotp_sub_right (p q r : Plane) : dotp p (q - r) = dotp p q - dotp p r := by
  simp only [dotp, PiLp.sub_apply]
  ring

theorem dotp_smul_right (a : ℝ) (p q : Plane) : dotp p (a • q) = a * dotp p q := by
  simp only [dotp, PiLp.smul_apply, smul_eq_mul]
  ring

theorem dotp_smul_left (a : ℝ) (p q : Plane) : dotp (a • p) q = a * dotp p q := by
  rw [dotp_comm, dotp_smul_right, dotp_comm q p]

private theorem eta (p : Plane) : point (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

theorem dist_sq_coordinates (p q : Plane) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  simpa only [eta] using dist_point_sq (p 0) (p 1) (q 0) (q 1)

def centroid (T : UnitTriangle) : Plane :=
  (1 / 3 : ℝ) • (T.vertex 0 + T.vertex 1 + T.vertex 2)

def centered (T : UnitTriangle) (i : Fin 3) : Plane := T.vertex i - centroid T

def normal (T : UnitTriangle) (i : Fin 3) : Plane := (-Real.sqrt 3) • centered T i

def offset (T : UnitTriangle) (i : Fin 3) : ℝ :=
  dotp (normal T i) (centroid T) + Real.sqrt 3 / 6

theorem centered_sum (T : UnitTriangle) :
    centered T 0 + centered T 1 + centered T 2 = 0 := by
  unfold centered centroid
  module

theorem centered_gram (T : UnitTriangle) (i j : Fin 3) :
    dotp (centered T i) (centered T j) = if i = j then (1 / 3 : ℝ) else -1 / 6 := by
  have h01 := dist_sq_coordinates (T.vertex 0) (T.vertex 1)
  have h02 := dist_sq_coordinates (T.vertex 0) (T.vertex 2)
  have h12 := dist_sq_coordinates (T.vertex 1) (T.vertex 2)
  rw [T.edgeLength 0 1 (by decide)] at h01
  rw [T.edgeLength 0 2 (by decide)] at h02
  rw [T.edgeLength 1 2 (by decide)] at h12
  fin_cases i <;> fin_cases j <;>
    norm_num [dotp, centered, centroid] <;> nlinarith

theorem normal_gram (T : UnitTriangle) (i j : Fin 3) :
    dotp (normal T i) (normal T j) = if i = j then (1 : ℝ) else -1 / 2 := by
  simp only [normal, dotp_smul_left, dotp_smul_right, centered_gram]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  split_ifs <;> nlinarith

theorem normal_sum (T : UnitTriangle) : normal T 0 + normal T 1 + normal T 2 = 0 := by
  simp only [normal, ← smul_add, centered_sum, smul_zero]

theorem normal_vertex_dot (T : UnitTriangle) (i j : Fin 3) :
    dotp (normal T i) (T.vertex j) =
      offset T i - (Real.sqrt 3 / 2) * (if i = j then 1 else 0) := by
  have hv : T.vertex j = centered T j + centroid T := by
    simp [centered]
  rw [hv, dotp_add_right]
  simp only [normal, dotp_smul_left, centered_gram, offset]
  split_ifs <;> ring

theorem offset_sum (T : UnitTriangle) :
    offset T 0 + offset T 1 + offset T 2 = Real.sqrt 3 / 2 := by
  have hsum := congrArg (fun n : Plane => dotp n (centroid T)) (normal_sum T)
  simp only [dotp, PiLp.add_apply, PiLp.zero_apply, zero_mul, add_zero] at hsum
  unfold offset dotp
  linarith

/-- Two unit vectors with mutual dot product `-1/2` separate points of the plane. -/
theorem eq_of_two_dot_eq {a b p q : Plane}
    (ha : dotp a a = 1) (hb : dotp b b = 1) (hab : dotp a b = -1 / 2)
    (hp : dotp a p = dotp a q) (hq : dotp b p = dotp b q) : p = q := by
  let D := a 0 * b 1 - a 1 * b 0
  have hD : D ^ 2 = 3 / 4 := by
    calc
      D ^ 2 = dotp a a * dotp b b - dotp a b ^ 2 := by unfold D dotp; ring
      _ = 3 / 4 := by rw [ha, hb, hab]; norm_num
  have hDne : D ≠ 0 := by intro hz; rw [hz] at hD; norm_num at hD
  have hx : D * (p 0 - q 0) = 0 := by
    calc
      D * (p 0 - q 0) = b 1 * (dotp a p - dotp a q) - a 1 * (dotp b p - dotp b q) := by
        unfold D dotp
        ring
      _ = 0 := by rw [hp, hq]; ring
  have hy : D * (p 1 - q 1) = 0 := by
    calc
      D * (p 1 - q 1) = a 0 * (dotp b p - dotp b q) - b 0 * (dotp a p - dotp a q) := by
        unfold D dotp
        ring
      _ = 0 := by rw [hp, hq]; ring
  have hx' := sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hDne)
  have hy' := sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hDne)
  ext i
  fin_cases i
  · exact hx'
  · exact hy'

def weight (T : UnitTriangle) (p : Plane) (i : Fin 3) : ℝ :=
  (offset T i - dotp (normal T i) p) / (Real.sqrt 3 / 2)

theorem weight_sum (T : UnitTriangle) (p : Plane) : ∑ i, weight T p i = 1 := by
  have hsum := congrArg (fun n : Plane => dotp n p) (normal_sum T)
  simp only [dotp, PiLp.add_apply, PiLp.zero_apply, zero_mul, add_zero] at hsum
  have hsum' : dotp (normal T 0) p + dotp (normal T 1) p + dotp (normal T 2) p = 0 := by
    unfold dotp
    linarith
  rw [Fin.sum_univ_three]
  unfold weight
  have hh : Real.sqrt 3 / 2 ≠ 0 := by positivity
  rw [← add_div, ← add_div]
  apply (div_eq_iff hh).mpr
  linarith [offset_sum T]

theorem weight_reconstruct (T : UnitTriangle) (p : Plane) :
    ∑ i, weight T p i • T.vertex i = p := by
  have hs := weight_sum T p
  rw [Fin.sum_univ_three] at hs ⊢
  have hh : Real.sqrt 3 / 2 ≠ 0 := by positivity
  have hw (j : Fin 3) : weight T p j * (Real.sqrt 3 / 2) =
      offset T j - dotp (normal T j) p := div_mul_cancel₀ _ hh
  have hdot (i : Fin 3) :
      dotp (normal T i)
          (weight T p 0 • T.vertex 0 + weight T p 1 • T.vertex 1 + weight T p 2 • T.vertex 2) =
        dotp (normal T i) p := by
    simp only [dotp_add_right, dotp_smul_right, normal_vertex_dot]
    fin_cases i <;> norm_num
    all_goals nlinarith [hw 0, hw 1, hw 2, congrArg (fun x : ℝ => x * offset T 0) hs,
      congrArg (fun x : ℝ => x * offset T 1) hs,
      congrArg (fun x : ℝ => x * offset T 2) hs]
  exact eq_of_two_dot_eq (by simpa using normal_gram T 0 0)
    (by simpa using normal_gram T 1 1) (by simpa using normal_gram T 0 1) (hdot 0) (hdot 1)

/-- The actual closed triangular region equals its three derived support halfplanes. -/
theorem mem_region_iff_halfplanes (T : UnitTriangle) (p : Plane) :
    p ∈ T.region ↔ ∀ i, dotp (normal T i) p ≤ offset T i := by
  constructor
  · intro hp i
    have hc : Convex ℝ {q : Plane | dotp (normal T i) q ≤ offset T i} := by
      intro x hx y hy a b ha hb hab
      change dotp (normal T i) (a • x + b • y) ≤ offset T i
      rw [dotp_add_right, dotp_smul_right, dotp_smul_right]
      calc
        a * dotp (normal T i) x + b * dotp (normal T i) y
            ≤ a * offset T i + b * offset T i :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
        _ = offset T i := by nlinarith [congrArg (fun z : ℝ => z * offset T i) hab]
    have hvertices : Set.range T.vertex ⊆ {q : Plane | dotp (normal T i) q ≤ offset T i} := by
      rintro _ ⟨j, rfl⟩
      change dotp (normal T i) (T.vertex j) ≤ offset T i
      rw [normal_vertex_dot]
      split_ifs <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]
    exact (convexHull_min hvertices hc) hp
  · intro hp
    apply mem_convexHull_of_exists_fintype (weight T p) T.vertex
    · intro i
      exact div_nonneg (sub_nonneg.mpr (hp i)) (by positivity)
    · exact weight_sum T p
    · intro i
      exact ⟨i, rfl⟩
    · exact weight_reconstruct T p

/-- Every actual triangle admits the same normal chart used by the interval
certificate, after relabelling its three support lines. -/
theorem normal_chart (T : UnitTriangle) :
    ∃ c d : ℝ, ∃ σ : Equiv.Perm (Fin 3),
      0 ≤ c ∧ c ^ 2 + d ^ 2 = 1 ∧
      ∀ i, ((normal T (σ i)) 0, (normal T (σ i)) 1) =
        NICertificate.normalValues c d i := by
  classical
  have hxsum := congrArg (fun p : Plane => p 0) (normal_sum T)
  simp only [PiLp.add_apply, PiLp.zero_apply] at hxsum
  have hex : ∃ k, 0 ≤ (normal T k) 0 := by
    by_contra h
    push Not at h
    linarith [h 0, h 1, h 2]
  obtain ⟨k, hk⟩ := hex
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 k
  let a := normal T (τ 0)
  let b := normal T (τ 1)
  let e := normal T (τ 2)
  have ha : 0 ≤ a 0 := by simpa [a, τ] using hk
  have haa : a 0 ^ 2 + a 1 ^ 2 = 1 := by
    simpa [a, dotp, pow_two] using normal_gram T (τ 0) (τ 0)
  have hbb : b 0 ^ 2 + b 1 ^ 2 = 1 := by
    simpa [b, dotp, pow_two] using normal_gram T (τ 1) (τ 1)
  have hne : τ 0 ≠ τ 1 := τ.injective.ne (by decide)
  have hab : a 0 * b 0 + a 1 * b 1 = -1 / 2 := by
    simpa [a, b, dotp, hne] using normal_gram T (τ 0) (τ 1)
  have hsorig : ∑ i, normal T i = 0 := by
    simpa only [Fin.sum_univ_three] using normal_sum T
  have hsperm : ∑ i, normal T (τ i) = 0 := (Equiv.sum_comp τ (normal T)).trans hsorig
  have hsum : a + b + e = 0 := by
    simpa only [Fin.sum_univ_three] using hsperm
  have hsx := congrArg (fun p : Plane => p 0) hsum
  have hsy := congrArg (fun p : Plane => p 1) hsum
  simp only [PiLp.add_apply, PiLp.zero_apply] at hsx hsy
  rcases ExtremeTriangle.other_normal_eq haa hbb hab with hb | hb
  · have he : (e 0, e 1) = NICertificate.normalValues (a 0) (a 1) 2 := by
      have hbx := congrArg Prod.fst hb
      have hby := congrArg Prod.snd hb
      apply Prod.ext <;> norm_num [NICertificate.normalValues] at hbx hby ⊢ <;> linarith
    refine ⟨a 0, a 1, τ, ha, haa, ?_⟩
    intro i
    fin_cases i
    · simp [NICertificate.normalValues, a]
    · exact hb
    · exact he
  · have he : (e 0, e 1) = NICertificate.normalValues (a 0) (a 1) 1 := by
      have hbx := congrArg Prod.fst hb
      have hby := congrArg Prod.snd hb
      apply Prod.ext <;> norm_num [NICertificate.normalValues] at hbx hby ⊢ <;> linarith
    refine ⟨a 0, a 1, (Equiv.swap 1 2).trans τ, ha, haa, ?_⟩
    intro i
    fin_cases i
    · simp [Equiv.trans_apply, Equiv.swap_apply_def, NICertificate.normalValues, a]
    · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using he
    · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using hb

/-- Exact actual-triangle-to-certificate bridge. No halfplane representation
hypothesis is added: the chart and offsets are constructed for every actual
unit equilateral triangle. -/
theorem exists_normal_frame (T : UnitTriangle) :
    ∃ c d : ℝ, ∃ b : Fin 3 → ℝ,
      0 ≤ c ∧ c ^ 2 + d ^ 2 = 1 ∧
      b 0 + b 1 + b 2 = NICertificate.halfRoot ∧
      ∀ p : Plane, p ∈ T.region ↔
        ExtremeTriangle.InHalfplanes (NICertificate.normalValues c d) b (p 0, p 1) := by
  obtain ⟨c, d, σ, hc, hu, hn⟩ := normal_chart T
  refine ⟨c, d, fun i => offset T (σ i), hc, hu, ?_, ?_⟩
  · have h := Equiv.sum_comp σ (offset T)
    simpa only [Fin.sum_univ_three, offset_sum, NICertificate.halfRoot] using
      h.trans (by simpa only [Fin.sum_univ_three] using offset_sum T)
  · intro p
    rw [mem_region_iff_halfplanes]
    constructor
    · intro hp i
      rw [← hn i]
      exact hp (σ i)
    · intro hp j
      obtain ⟨i, rfl⟩ := σ.surjective j
      have hi := hp i
      rw [← hn i] at hi
      exact hi

/-- The frozen Q25 interval certificate now applies to an actual arbitrary unit
triangle containing its three specified points. The resulting point is strictly
inside the open radius-`1/2` disk. -/
theorem q25_actual_triangle_invasion (T : UnitTriangle)
    (ha : point (-1 / 2) NICertificate.halfRoot ∈ T.region)
    (hb : point (-1) 0 ∈ T.region)
    (hp : point (-1 / 2) 0 ∈ T.region) :
    ∃ p ∈ T.region, ‖p‖ < (1 / 2 : ℝ) := by
  obtain ⟨c, d, b, hc, hu, hsum, hmem⟩ := exists_normal_frame T
  have hpoints : ∀ j : Fin 3,
      point (NICertificate.pointValues j).1 (NICertificate.pointValues j).2 ∈ T.region := by
    intro j
    fin_cases j
    · simpa [NICertificate.pointValues] using ha
    · simpa [NICertificate.pointValues] using hb
    · simpa [NICertificate.pointValues] using hp
  have hsupport : ∀ i j,
      NICertificate.dot (NICertificate.normalValues c d i) (NICertificate.pointValues j) ≤ b i := by
    intro i j
    simpa only [point_coord_zero, point_coord_one, Prod.eta] using
      ((hmem (point (NICertificate.pointValues j).1 (NICertificate.pointValues j).2)).mp
        (hpoints j) i)
  obtain ⟨q, hq, hnorm⟩ := ExtremeTriangle.q25_scalar_invasion hu hc b hsum hsupport
  refine ⟨point q.1 q.2, ?_, ?_⟩
  · apply (hmem _).mpr
    simpa only [point_coord_zero, point_coord_one, Prod.eta] using hq
  · have hs := norm_point_sq q.1 q.2
    have hn := norm_nonneg (point q.1 q.2)
    change q.1 ^ 2 + q.2 ^ 2 < 1 / 4 at hnorm
    nlinarith

/-- An actual triangle containing the Q25 triple cannot satisfy the asserted
radius-`1/2` nonintrusion condition. This proof consumes the interval certificate
through the derived exact normal frame. -/
theorem q25_actual_nonintrusion_impossible (T : UnitTriangle)
    (ha : point (-1 / 2) NICertificate.halfRoot ∈ T.region)
    (hb : point (-1) 0 ∈ T.region)
    (hp : point (-1 / 2) 0 ∈ T.region)
    (hNI : ∀ p ∈ T.region, (1 / 2 : ℝ) ≤ ‖p‖) : False := by
  obtain ⟨p, hpT, hpn⟩ := q25_actual_triangle_invasion T ha hb hp
  exact (not_le_of_gt hpn) (hNI p hpT)

end
end TriangleFrame
end HexagonCover
