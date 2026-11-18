import HexagonCover.BoundaryGaps
import HexagonCover.SourceCoordinates

/-! No-gap means that outer owners cover every entire closed side, even if C
also shares a point. This justifies source-tree outer-only boundary roles. -/
namespace HexagonCover.NoGap
open HexagonCover.Configuration BoundaryOwners BoundaryGaps
noncomputable section

theorem outer_edge_covered {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (nogaps : ∀i,¬gap h i) (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃j : Fin 6,edgePoint i t ∈ (config j.castSucc).region := by
  by_cases hle : t ≤ b h i
  · exact ⟨i,((rightReach h i).character t ht).mpr hle⟩
  · have hjoin := le_of_not_gt (nogaps i)
    change 1 ≤ b h i+a h (i+1) at hjoin
    have ht' : 1-t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    refine ⟨i+1,?_⟩
    rw [reversed_edge]
    apply ((leftReach h (i+1)).character (1-t) ht').mpr
    change 1-t ≤ a h (i+1)
    linarith

theorem source_outer_edge_covered {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (nogaps : ∀i,¬gap h i) (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃j : Fin 6,AffineMap.lineMap (SourceCoordinates.vertex i)
      (SourceCoordinates.vertex (i+1)) t ∈
      (SourceCoordinates.rotateConfig config j.castSucc).region := by
  obtain ⟨j,hj⟩ := outer_edge_covered h nogaps i ht
  refine ⟨j,?_⟩
  rw [SourceCoordinates.rotateConfig,Symmetry.map_region,
    ←SourceCoordinates.turn_vertex_eq,←SourceCoordinates.turn_vertex_eq,
    ←ReachEquiv.lineMap_apply]
  exact ⟨edgePoint i t,hj,rfl⟩

end
end HexagonCover.NoGap
