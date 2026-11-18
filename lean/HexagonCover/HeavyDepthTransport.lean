import HexagonCover.HeavyDepth
import HexagonCover.SourceCoordinates
import HexagonCover.NormalizedHeavy

/-! Whole finite depth of the same normalized source-coordinate heavy owner.
NormalizedHeavy has already reflected the entire placement when necessary to
make reach b5 the long reach. The subsequent +60-degree rotation keeps all role
labels and sends that exact edge to the upper edge from U=(1,0). No individual
piece is independently reflected or replaced in this transport. -/
namespace HexagonCover.HeavyDepthTransport
noncomputable section
open HexagonCover.Configuration NormalizedHeavy SourceCoordinates

theorem upper_lineMap (t : ℝ) : ExteriorLoss.upperEndpoint t=
    AffineMap.lineMap (vertex 5) (vertex ((5:Fin 6)+1)) t := by
  change ExteriorLoss.upperEndpoint t=
    AffineMap.lineMap (hexVertex 1 0) (hexVertex 1 1) t
  exact CornerTransport.upperEndpoint_eq_lineMap t

theorem lower_lineMap (t : ℝ) : ExteriorLoss.lowerEndpoint t=
    AffineMap.lineMap (vertex 5) (vertex ((5:Fin 6)-1)) t := by
  change ExteriorLoss.lowerEndpoint t=
    AffineMap.lineMap (hexVertex 1 0) (hexVertex 1 5) t
  exact CornerTransport.lowerEndpoint_eq_lineMap t

theorem anchor_ball {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    ∃r>0,Metric.ball ExteriorLoss.corner r ⊆ (rotateConfig config 5).region := by
  obtain ⟨r,hr,hb⟩ := h.cover.anchorBalls ((5:Fin 6).castSucc)
  rw [qAnchor_outer] at hb
  have hrot := CornerTransport.action_ball QSymmetry.rotationAction (config 5)
    (hexVertex 1 (5:Fin 6)) hb
  change Metric.ball (Symmetry.turn (hexVertex 1 (5:Fin 6))) r ⊆
    (rotateConfig config 5).region at hrot
  rw [turn_vertex_eq] at hrot
  change Metric.ball ExteriorLoss.corner r ⊆ (rotateConfig config 5).region at hrot
  exact ⟨r,hr,hrot⟩

theorem actual_endpoints {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    ExteriorLoss.upperEndpoint (M h)∈(rotateConfig config 5).region ∧
    ExteriorLoss.lowerEndpoint (a h.cover 5)∈(rotateConfig config 5).region := by
  constructor
  · rw [upper_lineMap]
    exact right_endpoint h.cover 5
      ⟨(rightReach h.cover 5).positive.le,(rightReach h.cover 5).lt_one.le⟩ le_rfl
  · rw [lower_lineMap]
    exact left_endpoint h.cover 5
      ⟨(leftReach h.cover 5).positive.le,(leftReach h.cover 5).lt_one.le⟩ le_rfl

/-- The normalized actual heavy5 has the strict whole-triangle W(M) bound in
the original N/source coordinates, including all finite vertices and sides. -/
theorem actual_source_depth {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (hM : 4/5 < M h) : ∀p∈(rotateConfig config 5).region,
      HeavyDepth.upperDepth p < HeavyDepth.W (M h) := by
  obtain ⟨_,_,hsum,_,hM1,_⟩ := structure_bounds h
  obtain ⟨r,hr,hball⟩ := anchor_ball h
  obtain ⟨hlong,hshort⟩ := actual_endpoints h
  have hdepth := HeavyDepth.actual_triangle_depth (rotateConfig config 5)
    (a := a h.cover 5) (M := M h) (leftReach h.cover 5).positive.le
    hsum.le hM hM1 hr hball hlong hshort
  intro p hp
  exact (hdepth p hp).2 hsum

end
end HexagonCover.HeavyDepthTransport
