import HexagonCover.HighMCentral
import HexagonCover.Symmetry

/-! Transport both residual points and the disk by one actual rigid motion
of the same central triangle. -/
namespace HexagonCover.HighMCentralMotion
noncomputable section
open TriangleFrame

theorem bound (T : UnitTriangle) {n : Plane} {D R q : ℝ}
    (hn : dotp n n=1) (hD : 0 < D) (hR : 0 ≤ R)
    (hball : Metric.closedBall (0:Plane) R ⊆ T.region)
    (hplus : D • n+(q*D) • point (n 1) (-n 0)∈T.region)
    (hminus : D • n+(-q*D) • point (n 1) (-n 0)∈T.region)
    (hcase : (q=1/5 ∧ R ≤ D/15) ∨ (q=21/100 ∧ R ≤ 9*D/100)) :
    D+2*R ≤ NICertificate.halfRoot := by
  have hu : (n 0)^2+(-n 1)^2=1 := by
    dsimp [dotp] at hn
    nlinarith only [hn]
  let f := RigidMotion.rotationIsometry (n 0) (-n 1) hu
  let T' := Symmetry.mapTriangle f.toAffineIsometryEquiv T
  have hrotate (k : ℝ) :
      f (D • n+(k*D) • point (n 1) (-n 0))=point D (-k*D) := by
    change RigidMotion.rotation (n 0) (-n 1) _=_
    ext i
    fin_cases i
    all_goals simp [RigidMotion.rotation,point]
    all_goals nlinarith only [congrArg (fun x:ℝ => D*x) hu,
      congrArg (fun x:ℝ => k*D*x) hu]
  have hball' : Metric.closedBall (0:Plane) R ⊆ T'.region := by
    intro p hp
    simp only [T',Symmetry.map_region]
    refine ⟨f.symm p,hball ?_,f.apply_symm_apply p⟩
    simpa only [Metric.mem_closedBall,dist_zero_right,f.symm.norm_map] using hp
  have hp' : point D (q*D)∈T'.region := by
    simp only [T',Symmetry.map_region]
    refine ⟨D • n+(-q*D) • point (n 1) (-n 0),hminus,?_⟩
    simpa only [LinearIsometryEquiv.coe_toAffineIsometryEquiv,neg_neg] using hrotate (-q)
  have hm' : point D (-q*D)∈T'.region := by
    simp only [T',Symmetry.map_region]
    exact ⟨D • n+(q*D) • point (n 1) (-n 0),hplus,hrotate q⟩
  exact HighMCentral.axis_bound T' hD hR hball' hp' hm' hcase

#print axioms bound
end
end HexagonCover.HighMCentralMotion
