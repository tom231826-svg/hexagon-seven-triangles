import HexagonCover.SupportGeometryWeak
import HexagonCover.EdgeReach

/-! Actual active-side extraction needed by the E4 T1/T2/T3 charts.
An attained maximum has an active actual halfplane. Every tied active side
has positive ray projection when the actual anchor contains an open ball. -/
namespace HexagonCover.E4InsideActive
noncomputable section
open TriangleFrame SupportGeometry

theorem strict_halfplanes_open (normal : Fin 3→Plane) (offs : Fin 3→ℝ) :
    IsOpen {p:Plane | ∀i,dotp (normal i) p < offs i} := by
  have he : {p:Plane | ∀i,dotp (normal i) p < offs i}=
      ⋂i:Fin 3,{p:Plane | dotp (normal i) p < offs i} := by ext p; simp
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_lt
  · unfold dotp
    fun_prop
  · fun_prop

theorem exists_active_at_reach (T : UnitTriangle) {u v : Plane}
    (reach : EdgeReach.Reach T u v) (normal : Fin 3→Plane) (offs : Fin 3→ℝ)
    (hmem : ∀p:Plane,p∈T.region ↔ ∀i,dotp (normal i) p ≤ offs i) :
    ∃i,dotp (normal i) (AffineMap.lineMap u v reach.length)=offs i := by
  have hend := (hmem _).mp reach.endpoint
  by_contra hn
  push Not at hn
  have hstrict : ∀i,dotp (normal i) (AffineMap.lineMap u v reach.length)<offs i :=
    fun i=>lt_of_le_of_ne (hend i) (hn i)
  let U : Set ℝ := (AffineMap.lineMap u v) ⁻¹'
    {p:Plane | ∀i,dotp (normal i) p < offs i}
  have hopen : IsOpen U := (strict_halfplanes_open normal offs).preimage
    (lipschitzWith_lineMap (𝕜:=ℝ) u v).continuous
  have ha : reach.length∈U := hstrict
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen reach.length ha
  let d : ℝ := min (ε/2) ((1-reach.length)/2)
  have hd : 0 < d := lt_min (by linarith) (by linarith [reach.lt_one])
  have hdε : d < ε := (min_le_left _ _).trans_lt (by linarith)
  have hda : reach.length+d ≤ 1 := by
    have hh := min_le_right (ε/2) ((1-reach.length)/2)
    change d ≤ (1-reach.length)/2 at hh
    linarith [reach.lt_one]
  have ht : reach.length+d∈U := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos hd]
    exact hdε
  have hm : AffineMap.lineMap u v (reach.length+d)∈T.region :=
    (hmem _).mpr (fun i=>(ht i).le)
  have hl := (reach.character (reach.length+d) ⟨by linarith [reach.positive],hda⟩).mp hm
  linarith

theorem anchor_margin_pos (T : UnitTriangle) {u : Plane} {r c d : ℝ}
    {offs : Fin 3→ℝ} (hr : 0 < r) (hball : Metric.ball u r ⊆ T.region)
    (hu : c^2+d^2=1)
    (hmem : ∀p:Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p ≤ offs i)
    (i : Fin 3) : 0 < offs i-dotp (nvec c d i) u := by
  have ht : 0 < r/2 := by linarith
  have hp : u+(r/2) • nvec c d i∈T.region := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos ht,ExteriorLoss.nvec_norm hu,mul_one]
    linarith
  have htest := (hmem _).mp hp i
  rw [dotp_add_right,dotp_smul_right,nvec_gram hu i i] at htest
  simp only [ite_true,mul_one] at htest
  linarith

/-- This applies to every active index, including all sides of an exit tie. -/
theorem active_projection_pos (T : UnitTriangle) {u v : Plane}
    (reach : EdgeReach.Reach T u v) {r c d : ℝ} {offs : Fin 3→ℝ}
    (hr : 0 < r) (hball : Metric.ball u r ⊆ T.region) (hu : c^2+d^2=1)
    (hmem : ∀p:Plane,p∈T.region ↔ ∀i,dotp (nvec c d i) p ≤ offs i)
    (i : Fin 3) (hactive : dotp (nvec c d i) (AffineMap.lineMap u v reach.length)=offs i) :
    0 < dotp (nvec c d i) (v-u) := by
  have hm := anchor_margin_pos T hr hball hu hmem i
  have he : dotp (nvec c d i) (AffineMap.lineMap u v reach.length)=
      dotp (nvec c d i) u+reach.length*dotp (nvec c d i) (v-u) := by
    simp [AffineMap.lineMap_apply,dotp]
    ring
  rw [he] at hactive
  nlinarith [reach.positive]

#print axioms exists_active_at_reach
#print axioms active_projection_pos

end
end HexagonCover.E4InsideActive
