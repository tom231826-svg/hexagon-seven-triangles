import HexagonCover.HexagonArea
import HexagonCover.SupportGeometry

/-! Actual geometric reduction for corner exterior loss.

This module does not yet identify the Lebesgue area of the clipped minimal
triangle with a polynomial formula. Its conclusions are geometric containment,
strict actual support inequalities, and genuine measure monotonicity.
The fresh derivation and subsequent source exposure are recorded separately.
-/

namespace HexagonCover.ExteriorLoss

noncomputable section

open MeasureTheory TriangleFrame SupportGeometry

def corner : Plane := point 1 0
def upperRay : Plane := point (-1 / 2) NICertificate.halfRoot
def lowerRay : Plane := point (-1 / 2) (-NICertificate.halfRoot)
def upperEndpoint (a : ℝ) : Plane := corner + a • upperRay
def lowerEndpoint (b : ℝ) : Plane := corner + b • lowerRay

/-- The entire inward corner cone, not a bounded polygon approximation. -/
def cornerCone : Set Plane :=
  {p | p 0 + p 1 / Real.sqrt 3 ≤ 1 ∧ p 0 - p 1 / Real.sqrt 3 ≤ 1}

theorem hexagon_subset_cornerCone : Hexagon 1 ⊆ cornerCone := by
  intro p hp
  have hu := StandardCover.hex_forms_bound hp 0
  have hv := StandardCover.hex_forms_bound hp 2
  constructor
  · exact hu
  · change p 0 - p 1 / Real.sqrt 3 ≤ 1
    have he : StandardCover.forms p 2 = p 0 - p 1 / Real.sqrt 3 := by
      simp [StandardCover.forms, StandardCover.coordU, StandardCover.coordV]
      ring
    rwa [he] at hv

theorem cone_loss_le_hexagon_loss (T : UnitTriangle) :
    volume.real (T.region \ cornerCone) ≤ volume.real (T.region \ Hexagon 1) := by
  refine measureReal_mono
    (Set.sdiff_subset_sdiff (Set.Subset.refl _) hexagon_subset_cornerCone) ?_
  exact measure_ne_top_of_subset Set.sdiff_subset T.compact_region.measure_ne_top

theorem nvec_norm {c d : ℝ} (hu : c ^ 2 + d ^ 2 = 1) (i : Fin 3) :
    ‖nvec c d i‖ = 1 := by
  have hg := nvec_gram hu i i
  simp only [ite_true] at hg
  have hn := norm_point_sq (NICertificate.normalValues c d i).1
    (NICertificate.normalValues c d i).2
  change ‖nvec c d i‖ ^ 2 = _ at hn
  change (nvec c d i) 0 * (nvec c d i) 0 +
    (nvec c d i) 1 * (nvec c d i) 1 = 1 at hg
  dsimp [nvec] at hg
  nlinarith [norm_nonneg (nvec c d i)]

/-- Offsets in coordinates translated to the actual corner. -/
def translatedSupport (c d : ℝ) (b : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  b i - dotp (nvec c d i) corner

theorem translated_support_sum {c d : ℝ} {b : Fin 3 → ℝ}
    (hsum : b 0 + b 1 + b 2 = NICertificate.halfRoot) :
    ∑ i : Fin 3, translatedSupport c d b i = NICertificate.halfRoot := by
  have hz := dot_nvec_sum c d corner
  simp only [Fin.sum_univ_three] at hz ⊢
  simp only [translatedSupport]
  linarith

theorem translated_membership (T : UnitTriangle) {c d : ℝ} {b : Fin 3 → ℝ}
    (hmem : ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ b i)
    (z : Plane) :
    corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ translatedSupport c d b i := by
  rw [hmem]
  apply forall_congr'
  intro i
  rw [dotp_add_right]
  unfold translatedSupport
  constructor <;> intro h <;> linarith

/-- A positive disk in this actual triangle forces every physical support
offset to be strictly positive; membership of the anchor alone is weaker. -/
theorem translated_support_pos (T : UnitTriangle) {c d : ℝ} {b : Fin 3 → ℝ}
    (hu : c ^ 2 + d ^ 2 = 1)
    (hmem : ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ b i)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (i : Fin 3) : 0 < translatedSupport c d b i := by
  have ht : 0 < r / 2 := by linarith
  have hp : corner + (r / 2) • nvec c d i ∈ Metric.ball corner r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, nvec_norm hu, mul_one]
    linarith
  have hm := (translated_membership T hmem _).mp (hball hp) i
  rw [dotp_smul_right, nvec_gram hu i i, ite_eq_left rfl, mul_one] at hm
  exact lt_of_lt_of_le ht hm

def minimumSupport (c d a b : ℝ) (i : Fin 3) : ℝ :=
  max 0 (max (a * dotp (nvec c d i) upperRay) (b * dotp (nvec c d i) lowerRay))

/-- The minimal three-halfplane triangle in the original physical plane. -/
def minimalRegion (c d a b : ℝ) : Set Plane :=
  {p | ∀ i, dotp (nvec c d i) (p - corner) ≤ minimumSupport c d a b i}

theorem minimumSupport_le (T : UnitTriangle) {c d a b : ℝ} {offs : Fin 3 → ℝ}
    (hmem : ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ offs i)
    (hcorner : corner ∈ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region)
    (i : Fin 3) : minimumSupport c d a b i ≤ translatedSupport c d offs i := by
  have h0 := (hmem corner).mp hcorner i
  have hA := (translated_membership T hmem (a • upperRay)).mp ha i
  have hB := (translated_membership T hmem (b • lowerRay)).mp hb i
  rw [dotp_smul_right] at hA hB
  apply max_le
  · unfold translatedSupport
    linarith
  · exact max_le hA hB

theorem minimalRegion_subset (T : UnitTriangle) {c d a b : ℝ} {offs : Fin 3 → ℝ}
    (hmem : ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ offs i)
    (hcorner : corner ∈ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    minimalRegion c d a b ⊆ T.region := by
  intro p hp
  apply (hmem p).mpr
  intro i
  have hi := (hp i).trans (minimumSupport_le T hmem hcorner ha hb i)
  rw [dotp_sub_right] at hi
  unfold translatedSupport at hi
  linarith

/-- Every input is about one actual triangle. The reduced set is a genuine
subset, and the bound uses its actual Lebesgue area. No area formula is assumed. -/
theorem actual_corner_reduction (T : UnitTriangle) {a b r : ℝ}
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    ∃ c d : ℝ, ∃ offs : Fin 3 → ℝ,
      0 ≤ c ∧ c ^ 2 + d ^ 2 = 1 ∧
      (∑ i : Fin 3, translatedSupport c d offs i) = NICertificate.halfRoot ∧
      (∀ i, 0 < translatedSupport c d offs i) ∧
      (∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ offs i) ∧
      (∀ i, minimumSupport c d a b i ≤ translatedSupport c d offs i) ∧
      (∑ i : Fin 3, minimumSupport c d a b i) ≤ NICertificate.halfRoot ∧
      minimalRegion c d a b ⊆ T.region ∧
      volume.real (minimalRegion c d a b \ cornerCone) ≤
        volume.real (T.region \ Hexagon 1) := by
  obtain ⟨c, d, offs, hc, hu, hsum, hm⟩ := exists_normal_frame T
  have hmem : ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ offs i := by
    intro p
    exact hm p
  have hcorner : corner ∈ T.region := hball (Metric.mem_ball_self hr)
  have hle := minimumSupport_le T hmem hcorner ha hb
  have hsub := minimalRegion_subset T hmem hcorner ha hb
  have hsum' := translated_support_sum (c := c) (d := d) hsum
  refine ⟨c, d, offs, hc, hu, hsum', translated_support_pos T hu hmem hr hball,
    hmem, hle, ?_, hsub, ?_⟩
  · calc
      (∑ i : Fin 3, minimumSupport c d a b i) ≤
          ∑ i : Fin 3, translatedSupport c d offs i :=
        Finset.sum_le_sum (fun i _ => hle i)
      _ = NICertificate.halfRoot := hsum'
  · refine measureReal_mono
      (Set.sdiff_subset_sdiff hsub hexagon_subset_cornerCone) ?_
    exact measure_ne_top_of_subset Set.sdiff_subset T.compact_region.measure_ne_top

end
end HexagonCover.ExteriorLoss
