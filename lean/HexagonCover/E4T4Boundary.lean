import HexagonCover.HighMResidual

/-! A general same-configuration contact argument for T4. An actual supporting
halfplane suffices; the contact need not be assumed to belong to the finite
outer edge. Every other closed outer is excluded in an actual neighborhood. -/
namespace HexagonCover.E4T4Boundary
noncomputable section
open TriangleFrame

theorem supporting_line_forced {config : Fin 7 → UnitTriangle}
    (cover : Covers 1 config) (owner : Fin 6) {p n : Plane} {d : ℝ}
    (hp : p∈interior (Hexagon 1)) (hn : 0 < dotp n n) (hline : dotp n p=d)
    (houter : ∀i:Fin 6,i≠owner → p∉(config i.castSucc).region)
    (hhalf : ∀q∈(config owner.castSucc).region,dotp n q ≤ d) :
    p∈(config 6).region := by
  classical
  by_contra hc
  let others : Set Plane := ⋃i:{j:Fin 7 // j≠owner.castSucc},(config i.val).region
  have hclosed : IsClosed others := isClosed_iUnion_of_finite
    (fun i:{j:Fin 7 // j≠owner.castSucc} => (config i.val).closed_region)
  have hopen : IsOpen (interior (Hexagon 1) \ others) := isOpen_interior.sdiff hclosed
  have hpopen : p∈interior (Hexagon 1) \ others := by
    refine ⟨hp,?_⟩
    intro hmem
    obtain ⟨⟨j,hj⟩,hpj⟩ := Set.mem_iUnion.mp hmem
    by_cases hj6 : j=6
    · exact hc (by simpa only [hj6] using hpj)
    · have hjlt : j.val<6 := by omega
      let i : Fin 6 := ⟨j.val,hjlt⟩
      have hij : i.castSucc=j := by ext; rfl
      have hi : i≠owner := by
        intro he
        apply hj
        rw [←hij,he]
      exact houter i hi (by simpa only [hij] using hpj)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen p hpopen
  have hnorm : 0 < ‖n‖+1 := by linarith [norm_nonneg n]
  let δ : ℝ := ε/(2*(‖n‖+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ*(‖n‖+1)=ε/2 := by
    dsimp [δ]
    field_simp [ne_of_gt hnorm]
  let q : Plane := p+δ • n
  have hdist : dist q p=δ*‖n‖ := by
    rw [dist_eq_norm]
    have he : q-p=δ • n := by dsimp [q]; module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
  have hqopen : q∈interior (Hexagon 1) \ others := by
    apply hball
    rw [Metric.mem_ball,hdist]
    nlinarith only [hδeq,hδ,hε]
  obtain ⟨j,hqj⟩ := Set.mem_iUnion.mp (cover (interior_subset hqopen.1))
  have hjowner : j=owner.castSucc := by
    by_contra hj
    exact hqopen.2 (Set.mem_iUnion.mpr ⟨⟨j,hj⟩,hqj⟩)
  have hs := hhalf q (by simpa only [hjowner] using hqj)
  have he : dotp n q=d+δ*dotp n n := by
    dsimp [q]
    rw [dotp_add_right,dotp_smul_right,hline]
  rw [he] at hs
  linarith [mul_pos hδ hn]

#print axioms supporting_line_forced
end
end HexagonCover.E4T4Boundary
