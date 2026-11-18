import HexagonCover.BoundaryGaps
import HexagonCover.SourceCoordinates

/-! Rotate the SAME closed central gap obligation into the frozen source frame. -/
namespace HexagonCover.SourceGap
open Configuration SourceCoordinates BoundaryGaps BoundaryOwners
noncomputable section

theorem closed {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) (hi : gap h i) {t : ℝ}
    (ht : t∈Set.Icc (b h i) (1-a h (i+1))) :
    AffineMap.lineMap (vertex i) (vertex (i+1)) t∈(rotateConfig config 6).region := by
  have hp := closed_gap_central h i hi t ht
  rw [rotateConfig,Symmetry.map_region,←turn_vertex_eq,←turn_vertex_eq,
    ←ReachEquiv.lineMap_apply]
  exact ⟨edgePoint i t,hp,rfl⟩

theorem right_endpoint {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) (hi : gap h i) :
    AffineMap.lineMap (vertex i) (vertex (i+1)) (b h i)∈(rotateConfig config 6).region := by
  apply closed h i hi
  constructor
  · exact le_rfl
  · change b h i+a h (i+1)<1 at hi
    linarith

theorem left_endpoint {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) (hi : gap h i) :
    AffineMap.lineMap (vertex (i+1)) (vertex i) (a h (i+1))∈(rotateConfig config 6).region := by
  have hm := closed h i hi (t:=1-a h (i+1))
    ⟨by change b h i+a h (i+1)<1 at hi; linarith,le_rfl⟩
  have he : AffineMap.lineMap (vertex (i+1)) (vertex i) (a h (i+1))=
      AffineMap.lineMap (vertex i) (vertex (i+1)) (1-a h (i+1)) := by
    simp only [AffineMap.lineMap_apply_module]
    module
  rwa [he]

end
end HexagonCover.SourceGap
