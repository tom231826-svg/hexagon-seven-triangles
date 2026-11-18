import HexagonCover.SemanticEquivalence
import HexagonCover.FinalTheorem

/-! A geometric reading of the final theorem, proved equivalent to the exact
canonical proposition. Every triangle has its own arbitrary translation and
proper rotation. The hexagon may have any global affine-isometric pose.
All covered regions are the full closed shapes, and no disjointness,
distinctness, containment, symmetry or contact assumptions are imposed. -/
namespace HexagonCover.SemanticFinal
noncomputable section
open RigidMotion Symmetry SemanticEquivalence

/-- The seven placements are independent; repeated placements are permitted. -/
def RigidPlacementConjecture : Prop :=
  ∀ s : ℝ,1<s → ∀ hexPose : Plane ≃ᵃⁱ[ℝ] Plane,
    ∀ translations : Fin 7 → Plane,∀ c d : Fin 7 → ℝ,
      ∀ unit : ∀i,c i^2+d i^2=1,
        ¬hexPose '' Hexagon s ⊆
          ⋃i,rigid (translations i) (c i) (d i) (unit i) '' standardRegion

theorem rigid_statement_of_canonical (h : CoverConjecture) : RigidPlacementConjecture := by
  intro s hs hexPose translations c d unit hcover
  let config : Fin 7 → UnitTriangle := fun i=>
    mapTriangle (rigid (translations i) (c i) (d i) (unit i)) (StandardCover.fan 0)
  have hc : hexPose '' Hexagon s ⊆ ⋃i,(config i).region := by
    simpa only [config,map_region,←standard_region_eq_fan_zero] using hcover
  exact h s hs (fun i=>mapTriangle hexPose.symm (config i))
    ((moved_hexagon_cover_iff hexPose s config).mp hc)

theorem canonical_of_rigid_statement (h : RigidPlacementConjecture) : CoverConjecture := by
  classical
  intro s hs config hc
  choose translations c d unit hregion using
    (fun i : Fin 7=>exists_region_rigid_motion (config i))
  apply h s hs (AffineIsometryEquiv.refl ℝ Plane) translations c d unit
  change (id : Plane → Plane) '' Hexagon s ⊆
    ⋃i,rigid (translations i) (c i) (d i) (unit i) '' standardRegion
  rw [Set.image_id]
  simpa only [Covers,hregion] using hc

/-- The natural rigid-placement formulation and the formal canonical target
have both directions proved, so neither is a weakened substitute. -/
theorem original_statement_iff : CoverConjecture ↔ RigidPlacementConjecture :=
  ⟨rigid_statement_of_canonical,canonical_of_rigid_statement⟩

theorem no_cover_moved_hexagon (s : ℝ) (hs : 1<s)
    (hexPose : Plane ≃ᵃⁱ[ℝ] Plane) (config : Fin 7 → UnitTriangle) :
    ¬hexPose '' Hexagon s ⊆ ⋃i,(config i).region := by
  intro hc
  exact FinalTheorem.no_seven_cover s hs (fun i=>mapTriangle hexPose.symm (config i))
    ((moved_hexagon_cover_iff hexPose s config).mp hc)

/-- The original geometric statement, with no auxiliary proof premise. -/
theorem no_seven_rigid_placements : RigidPlacementConjecture :=
  original_statement_iff.mp FinalTheorem.cover_conjecture

theorem explicit_no_seven_rigid_placements (s : ℝ) (hs : 1<s)
    (hexPose : Plane ≃ᵃⁱ[ℝ] Plane) (translations : Fin 7 → Plane)
    (c d : Fin 7 → ℝ) (unit : ∀i,c i^2+d i^2=1) :
    ¬hexPose '' Hexagon s ⊆
      ⋃i,rigid (translations i) (c i) (d i) (unit i) '' standardRegion :=
  no_seven_rigid_placements s hs hexPose translations c d unit

#print axioms original_statement_iff
#print axioms no_cover_moved_hexagon
#print axioms no_seven_rigid_placements
#print axioms explicit_no_seven_rigid_placements
end
end HexagonCover.SemanticFinal
