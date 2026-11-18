import HexagonCover.ClippedCornerArea

/-! Actual heavy-reach separation from the origin. The proof is source-exposed
and constructs a uniform supporting-plane distance for the same triangle.
No perpendicular-foot membership or finite-side extension is assumed. -/

namespace HexagonCover.HeavyReach

noncomputable section

open TriangleFrame SupportGeometry ExteriorLoss CornerChart ClippedCornerArea

theorem support_separation {c x a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 0 < c) (hx : 0 < x) (hx1 : x ≤ 1)
    (hidentity : c ^ 2 * Q x = NICertificate.halfRoot ^ 2)
    (hsum : offs 0 + offs 1 + offs 2 = NICertificate.halfRoot)
    (h0 : c * (a * x) ≤ offs 0) (h1 : c * a ≤ offs 1)
    (h2 : c * b ≤ offs 2) (h1b : c * (b * x) ≤ offs 1)
    (hab : 1 ≤ a + b) :
    NICertificate.halfRoot * max a b ≤ c * (1 + x) - offs 1 ∧
      (1 < a + b → NICertificate.halfRoot * max a b < c * (1 + x) - offs 1) := by
  have hh := ExtremeTriangle.halfRoot_pos
  have hcx : 0 < c * x := mul_pos hc hx
  have hgap : 0 ≤ c * (a + b - 1) := mul_nonneg hc.le (by linarith)
  have hgapx : 0 ≤ c * x * (a + b - 1) := mul_nonneg hcx.le (by linarith)
  have hfeasa : a * (c * x) ≤ NICertificate.halfRoot - c := by nlinarith
  have hfeasb : b * c ≤ NICertificate.halfRoot - c * x := by nlinarith
  have hhgtc : c < NICertificate.halfRoot := by
    have hp : 0 < c ^ 2 * x * (1 + x) :=
      mul_pos (mul_pos (sq_pos_of_pos hc) hx) (by linarith)
    unfold Q at hidentity
    nlinarith
  have hKa : 0 < NICertificate.halfRoot + c * (1 - x) :=
    add_pos_of_pos_of_nonneg hh (mul_nonneg hc.le (sub_nonneg.mpr hx1))
  have hKb : 0 < NICertificate.halfRoot - c + c * x := by linarith
  have he1 : (NICertificate.halfRoot + c * (1 - x)) * (NICertificate.halfRoot - c) =
      (c * x) * (c * (2 + x) - NICertificate.halfRoot) := by
    unfold Q at hidentity
    nlinarith
  have he2 : (NICertificate.halfRoot - c + c * x) * (NICertificate.halfRoot - c * x) =
      c * (c * (1 + 2 * x) - NICertificate.halfRoot) := by
    unfold Q at hidentity
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_left hfeasa hKa.le
  have hm2 := mul_le_mul_of_nonneg_left hfeasb hKb.le
  rw [he1] at hm1
  rw [he2] at hm2
  have hkey1 : (NICertificate.halfRoot + c * (1 - x)) * a ≤
      c * (2 + x) - NICertificate.halfRoot := by
    apply (mul_le_mul_iff_of_pos_left hcx).mp
    nlinarith
  have hkey2 : (NICertificate.halfRoot - c + c * x) * b ≤
      c * (1 + 2 * x) - NICertificate.halfRoot := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    nlinarith
  have ha : NICertificate.halfRoot * a ≤ c * (1 + x) - offs 1 := by nlinarith
  have hb : NICertificate.halfRoot * b ≤ c * (1 + x) - offs 1 := by nlinarith
  constructor
  · by_cases hab' : a ≤ b
    · rwa [max_eq_right hab']
    · rwa [max_eq_left (le_of_lt (lt_of_not_ge hab'))]
  · intro hab'
    have hgap' : 0 < c * (a + b - 1) := mul_pos hc (by linarith)
    have hgapx' : 0 < c * x * (a + b - 1) := mul_pos hcx (by linarith)
    have ha' : NICertificate.halfRoot * a < c * (1 + x) - offs 1 := by nlinarith
    have hb' : NICertificate.halfRoot * b < c * (1 + x) - offs 1 := by nlinarith
    by_cases hab'' : a ≤ b
    · rwa [max_eq_right hab'']
    · rwa [max_eq_left (le_of_lt (lt_of_not_ge hab''))]

theorem dotp_le_norm {n : Plane} (hn : ‖n‖ = 1) (p : Plane) : dotp n p ≤ ‖p‖ := by
  have he : dotp n p = inner ℝ n p := by
    simp [dotp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    ring
  rw [he]
  simpa only [hn, one_mul] using real_inner_le_norm n p

theorem corner_projection {c d x : ℝ} (hc : c ≠ 0) (hparam : parameter c d = x) :
    dotp (nvec c d 1) corner = -c * (1 + x) := by
  have he : corner = conePoint 1 1 := by
    ext i
    fin_cases i <;> norm_num [corner, conePoint]
  rw [he, chart_dot hc, hparam]
  norm_num
  ring

theorem charted_separation (T : UnitTriangle) {c d a b : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1 / 2 ≤ c) (hd : 0 ≤ d) (hu : c ^ 2 + d ^ 2 = 1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : 1 ≤ a + b)
    (hsum : offs 0 + offs 1 + offs 2 = NICertificate.halfRoot)
    (hpos : ∀ i, 0 < offs i)
    (hmem : ∀ z : Plane, corner + z ∈ T.region ↔ ∀ i, dotp (nvec c d i) z ≤ offs i)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    ∃ D : ℝ, NICertificate.halfRoot * max a b ≤ D ∧
      (1 < a + b → NICertificate.halfRoot * max a b < D) ∧
      ∀ p ∈ T.region, D ≤ ‖p‖ := by
  let x := parameter c d
  have hcpos : 0 < c := by linarith
  have hparam : parameter c d = x := rfl
  have hxr : -1 / 2 ≤ x ∧ x ≤ 1 := parameter_bounds hc hd hu
  obtain ⟨h0, h1, h2, h1b⟩ := endpoint_support_bounds T (ne_of_gt hcpos) hparam hmem ha hb
  have hfeas := chart_feasibility hcpos hu hparam ha0 hb0 hsum (hpos 0) h0 h1 h2 h1b
  have hx : 0 < x := by
    by_contra hn
    have hlt := negative_chart_sum_lt_one hxr.1 (le_of_not_gt hn) hfeas.1
    linarith
  have hidentity : c ^ 2 * Q x = NICertificate.halfRoot ^ 2 := by
    rw [ExtremeTriangle.halfRoot_sq]
    exact parameter_identity hcpos hu
  have hsep := support_separation hcpos hx hxr.2 hidentity hsum h0 h1 h2 h1b hab
  refine ⟨c * (1 + x) - offs 1, hsep.1, hsep.2, ?_⟩
  intro p hp
  have hi := (hmem (p - corner)).mp (by simpa using hp) 1
  rw [dotp_sub_right, corner_projection (ne_of_gt hcpos) hparam] at hi
  have hnorm : ‖-nvec c d 1‖ = 1 := by rw [norm_neg, nvec_norm hu]
  have hd := dotp_le_norm hnorm p
  have he : dotp (-nvec c d 1) p = -dotp (nvec c d 1) p := by
    simp [dotp]
    ring
  rw [he] at hd
  nlinarith

theorem separation_from_frame (T : UnitTriangle) {c d a b r : ℝ} {offs : Fin 3 → ℝ}
    (hc : 1 / 2 ≤ c) (hd : 0 ≤ d) (hu : c ^ 2 + d ^ 2 = 1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : 1 ≤ a + b)
    (hsum : offs 0 + offs 1 + offs 2 = NICertificate.halfRoot)
    (hmem : ∀ p : Plane, p ∈ T.region ↔ ∀ i, dotp (nvec c d i) p ≤ offs i)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    ∃ D : ℝ, NICertificate.halfRoot * max a b ≤ D ∧
      (1 < a + b → NICertificate.halfRoot * max a b < D) ∧
      ∀ p ∈ T.region, D ≤ ‖p‖ := by
  have hsum' : translatedSupport c d offs 0 + translatedSupport c d offs 1 +
      translatedSupport c d offs 2 = NICertificate.halfRoot := by
    simpa only [Fin.sum_univ_three] using translated_support_sum (c := c) (d := d) hsum
  exact charted_separation T hc hd hu ha0 hb0 hab hsum'
    (translated_support_pos T hu hmem hr hball) (translated_membership T hmem) ha hb

theorem reflection_norm (p : Plane) : ‖reflect p‖ = ‖p‖ := by
  have h := reflection_dist p 0
  simpa [reflect] using h

/-- A uniform distance witness for one actual heavy triangle, valid at all
orientations. If the reach sum is strictly above one, the witness is strictly
larger than `sqrt(3)/2 * max a b`. -/
theorem actual_heavy_reach_separation (T : UnitTriangle) {a b r : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : 1 ≤ a + b)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region) :
    ∃ D : ℝ, NICertificate.halfRoot * max a b ≤ D ∧
      (1 < a + b → NICertificate.halfRoot * max a b < D) ∧
      ∀ p ∈ T.region, D ≤ ‖p‖ := by
  obtain ⟨flip, c, d, offs, hc, hd, hu, hsum, hmem⟩ := exists_corner_frame T
  cases flip
  · exact separation_from_frame T hc hd hu ha0 hb0 hab hsum hmem hr hball ha hb
  · have hmemR : ∀ p : Plane, p ∈ (reflectedTriangle T).region ↔
        ∀ i, dotp (nvec c d i) p ≤ offs i := by
      intro p
      rw [reflectedTriangle_mem_iff, hmem]
      simp only [maybeReflect, ite_true, reflect_reflect]
    have hA : upperEndpoint b ∈ (reflectedTriangle T).region := by
      rw [reflectedTriangle_region]
      exact ⟨lowerEndpoint b, hb, reflection_lowerEndpoint b⟩
    have hB : lowerEndpoint a ∈ (reflectedTriangle T).region := by
      rw [reflectedTriangle_region]
      exact ⟨upperEndpoint a, ha, reflection_upperEndpoint a⟩
    obtain ⟨D, hD, hDs, hP⟩ := separation_from_frame (reflectedTriangle T) hc hd hu
      hb0 ha0 (by linarith) hsum hmemR hr (reflectedTriangle_ball T hball) hA hB
    refine ⟨D, ?_, ?_, ?_⟩
    · simpa only [max_comm b a] using hD
    · intro hab'
      simpa only [max_comm b a] using hDs (by linarith)
    · intro p hp
      have hm : reflect p ∈ (reflectedTriangle T).region := by
        rw [reflectedTriangle_region]
        exact ⟨p, hp, rfl⟩
      simpa only [reflection_norm] using hP (reflect p) hm

theorem actual_heavy_avoids_radius (T : UnitTriangle) {a b r L : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : 1 ≤ a + b)
    (hr : 0 < r) (hball : Metric.ball corner r ⊆ T.region)
    (ha : upperEndpoint a ∈ T.region) (hb : lowerEndpoint b ∈ T.region)
    (hL : L ≤ max a b) : ∀ p ∈ T.region, NICertificate.halfRoot * L ≤ ‖p‖ := by
  obtain ⟨D, hD, _, hP⟩ := actual_heavy_reach_separation T ha0 hb0 hab hr hball ha hb
  intro p hp
  exact (mul_le_mul_of_nonneg_left hL ExtremeTriangle.halfRoot_pos.le).trans (hD.trans (hP p hp))

end
end HexagonCover.HeavyReach
