import HexagonCover.E4InsideActive
import HexagonCover.SourceCoordinates

/-! Active actual source-coordinate exits of the one given configuration.
The entire reach record is transported by the existing common +60° isometry;
its character/maximality is retained, not replaced by endpoint inclusion. -/
namespace HexagonCover.E4InsideSourceActive
noncomputable section
open TriangleFrame SupportGeometry
open HexagonCover.Configuration SourceCoordinates

theorem source_anchor_ball {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) : ∃r>0,Metric.ball (vertex i) r ⊆ (rotateConfig config i.castSucc).region := by
  obtain ⟨r,hr,hb⟩ := h.anchorBalls i.castSucc
  rw [qAnchor_outer] at hb
  have hrot := CornerTransport.action_ball QSymmetry.rotationAction (config i.castSucc)
    (hexVertex 1 i) hb
  change Metric.ball (Symmetry.turn (hexVertex 1 i)) r ⊆
    (rotateConfig config i.castSucc).region at hrot
  rw [turn_vertex_eq] at hrot
  exact ⟨r,hr,hrot⟩

theorem left_active {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6)
    {c d : ℝ} {offs : Fin 3→ℝ} (hu : c^2+d^2=1)
    (hmem : ∀p:Plane,p∈(rotateConfig config i.castSucc).region ↔
      ∀j,dotp (nvec c d j) p ≤ offs j) :
    ∃j,0 < dotp (nvec c d j) (vertex (i-1)-vertex i) ∧
      dotp (nvec c d j) (AffineMap.lineMap (vertex i) (vertex (i-1)) (a h i))=offs j := by
  let R := ReachEquiv.mapReach Symmetry.turn (leftReach h i)
  obtain ⟨r,hr,hball⟩ := source_anchor_ball h i
  have hb : Metric.ball (Symmetry.turn (hexVertex 1 i)) r ⊆
      (rotateConfig config i.castSucc).region := by simpa only [turn_vertex_eq] using hball
  obtain ⟨j,hj⟩ := E4InsideActive.exists_active_at_reach
    (rotateConfig config i.castSucc) R (nvec c d) offs hmem
  have hp := E4InsideActive.active_projection_pos
    (rotateConfig config i.castSucc) R hr hb hu hmem j hj
  refine ⟨j,?_,?_⟩
  · simpa only [turn_vertex_eq] using hp
  · simpa only [R,ReachEquiv.mapReach,turn_vertex_eq,a] using hj

theorem right_active {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6)
    {c d : ℝ} {offs : Fin 3→ℝ} (hu : c^2+d^2=1)
    (hmem : ∀p:Plane,p∈(rotateConfig config i.castSucc).region ↔
      ∀j,dotp (nvec c d j) p ≤ offs j) :
    ∃j,0 < dotp (nvec c d j) (vertex (i+1)-vertex i) ∧
      dotp (nvec c d j) (AffineMap.lineMap (vertex i) (vertex (i+1)) (b h i))=offs j := by
  let R := ReachEquiv.mapReach Symmetry.turn (rightReach h i)
  obtain ⟨r,hr,hball⟩ := source_anchor_ball h i
  have hb : Metric.ball (Symmetry.turn (hexVertex 1 i)) r ⊆
      (rotateConfig config i.castSucc).region := by simpa only [turn_vertex_eq] using hball
  obtain ⟨j,hj⟩ := E4InsideActive.exists_active_at_reach
    (rotateConfig config i.castSucc) R (nvec c d) offs hmem
  have hp := E4InsideActive.active_projection_pos
    (rotateConfig config i.castSucc) R hr hb hu hmem j hj
  refine ⟨j,?_,?_⟩
  · simpa only [turn_vertex_eq] using hp
  · simpa only [R,ReachEquiv.mapReach,turn_vertex_eq,b] using hj

#print axioms left_active
#print axioms right_active

end
end HexagonCover.E4InsideSourceActive
