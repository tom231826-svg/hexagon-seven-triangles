import HexagonCover.SourceCoordinates
import HexagonCover.TriangleFrame

/-! Source-exposed high-M review. A point on a support line of the heavy
triangle is forced into the same actual central triangle when it is interior
to the hexagon and strictly misses the other five outer triangles. The proof
uses closedness of those pieces and the central piece, so contact with the
heavy triangle is allowed; the line itself need not be uncovered. -/
namespace HexagonCover.HighMResidual
noncomputable section
open TriangleFrame

/-- The heavy triangle can touch `p`. Moving a sufficiently small positive
distance through its supporting line forces a nearby point into the same
central triangle; closedness is used via the open complement. -/
theorem supporting_line_forced {config : Fin 7 → UnitTriangle}
    (cover : Covers 1 config) {p n : Plane} {d : ℝ}
    (hp : p ∈ interior (Hexagon 1))
    (hunit : dotp n n = 1) (hline : dotp n p = d)
    (houter : ∀ i : Fin 6, i ≠ 5 → p ∉ (config i.castSucc).region)
    (hhalf : ∀ q ∈ (config 5).region, d ≤ dotp n q) :
    p ∈ (config 6).region := by
  classical
  by_contra hc
  let others : Set Plane := ⋃ i : {j : Fin 7 // j ≠ 5}, (config i.val).region
  have hclosed : IsClosed others := isClosed_iUnion_of_finite
    (fun i : {j : Fin 7 // j ≠ 5} => (config i.val).closed_region)
  have hopen : IsOpen (interior (Hexagon 1) \ others) := isOpen_interior.sdiff hclosed
  have hpopen : p ∈ interior (Hexagon 1) \ others := by
    refine ⟨hp, ?_⟩
    intro hmem
    obtain ⟨⟨j, hj⟩, hpj⟩ := Set.mem_iUnion.mp hmem
    by_cases hj6 : j = 6
    · exact hc (by simpa only [hj6] using hpj)
    · have hjlt : j.val < 6 := by omega
      let i : Fin 6 := ⟨j.val, hjlt⟩
      have hij : i.castSucc = j := by ext; rfl
      have hi5 : i ≠ 5 := by
        intro he
        apply hj
        rw [← hij, he]
        rfl
      exact houter i hi5 (by simpa only [hij] using hpj)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen p hpopen
  have hnormsq : ‖n‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [Fin.sum_univ_two, dotp, pow_two] using hunit
  have hnorm : ‖n‖ = 1 := by nlinarith [norm_nonneg n]
  let q : Plane := p - (ε / 2) • n
  have hdist : dist q p = ε / 2 := by
    rw [dist_eq_norm]
    have he : q - p = -((ε / 2) • n) := by dsimp [q]; module
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hnorm]
    ring
  have hqopen : q ∈ interior (Hexagon 1) \ others :=
    hball (by rw [Metric.mem_ball, hdist]; linarith)
  obtain ⟨j, hqj⟩ := Set.mem_iUnion.mp (cover (interior_subset hqopen.1))
  have hj5 : j = 5 := by
    by_contra hj
    exact hqopen.2 (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hqj⟩)
  have hsupport := hhalf q (by simpa only [hj5] using hqj)
  have hvalue : dotp n q = d - ε / 2 := by
    dsimp only [q]
    rw [dotp_sub_right, dotp_smul_right, hunit, hline]
    ring
  rw [hvalue] at hsupport
  linarith

/-- A squared-distance certificate to any actual point of a triangle gives
the strict outer exclusion required by `supporting_line_forced`. -/
theorem exclude_by_actual_point (T : UnitTriangle) {p a : Plane}
    (ha : a ∈ T.region) (hfar : 1 < dist p a ^ 2) : p ∉ T.region := by
  intro hp
  have hd := T.dist_le_one hp ha
  have hs : dist p a ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr hd
  linarith

end
end HexagonCover.HighMResidual

#print axioms HexagonCover.HighMResidual.supporting_line_forced
#print axioms HexagonCover.HighMResidual.exclude_by_actual_point
