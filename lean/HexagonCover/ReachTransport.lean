import HexagonCover.CornerTransport
import HexagonCover.CommonReach

namespace HexagonCover.ReachTransport
open CornerTransport QSymmetry Symmetry HexagonCover.Configuration
noncomputable section

theorem pullback_separation (action : Action) (T : UnitTriangle) {d : ℝ}
    (sep : ∀ q ∈ (mapTriangle action.motion T).region, d ≤ ‖q‖) :
    ∀ p ∈ T.region, d ≤ ‖p‖ := by
  intro p hp
  have h := sep (action.motion p) (by rw [map_region]; exact ⟨p,hp,rfl⟩)
  simpa only [action.norm] using h

theorem common_reach_at (i : Fin 6) (T : UnitTriangle) {t : ℝ} (ht : 0 ≤ t)
    (anchor : hexVertex 1 i ∈ T.region)
    (left : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) t ∈ T.region)
    (right : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t ∈ T.region) :
    ∀ p ∈ T.region, CommonReach.rho t ≤ ‖p‖ := by
  let action := inverse (rotationPower i.val)
  let rotated := mapTriangle action.motion T
  apply pullback_separation action T
  apply CommonReach.actual_common_reach_separation rotated ht
  · rw [map_region]
    exact ⟨hexVertex 1 i, anchor, inverse_corner i⟩
  · rw [map_region]
    refine ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t, right, ?_⟩
    rw [← rotation_upperEndpoint]
    exact (rotationPower i.val).motion.symm_apply_apply _
  · rw [map_region]
    refine ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) t, left, ?_⟩
    rw [← rotation_lowerEndpoint]
    exact (rotationPower i.val).motion.symm_apply_apply _

theorem actual_reach_separation {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) {t : ℝ} (ht : 0 ≤ t)
    (lower : t ≤ min (a h i) (b h i)) :
    ∀ p ∈ (config i.castSucc).region, CommonReach.rho t ≤ ‖p‖ := by
  have hta := lower.trans (min_le_left _ _)
  have htb := lower.trans (min_le_right _ _)
  have ht1 : t ≤ 1 := hta.trans (leftReach h i).lt_one.le
  apply common_reach_at i (config i.castSucc) ht
  · have hh := anchor_mem h i.castSucc
    simpa only [qAnchor_outer] using hh
  · exact ((leftReach h i).character t ⟨ht,ht1⟩).mpr hta
  · exact ((rightReach h i).character t ⟨ht,ht1⟩).mpr htb

end
end HexagonCover.ReachTransport
