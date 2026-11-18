import HexagonCover.Symmetry
import HexagonCover.Configuration

/-! Explicit dihedral actions on the entire actual configuration. The final
theorem here is conditional on the three Q exclusions; those exclusions are not
assumed globally and this file does not prove CoverConjecture. -/
namespace HexagonCover.QSymmetry
open Symmetry Normalization
noncomputable section

structure Action where
  motion : Plane ≃ᵃⁱ[ℝ] Plane
  roles : Equiv.Perm (Fin 7)
  zero : motion 0 = 0
  hexagon : motion '' Hexagon 1 = Hexagon 1
  anchors : ∀ i, motion (qAnchor 1 i) = qAnchor 1 (roles i)

def Action.transform (a : Action) (config : Fin 7 → UnitTriangle) : Fin 7 → UnitTriangle :=
  fun i => mapTriangle a.motion (config (a.roles.symm i))

theorem Action.norm (a : Action) (p : Plane) : ‖a.motion p‖ = ‖p‖ := by
  simpa only [a.zero, dist_zero_right] using a.motion.isometry.dist_eq p 0

theorem Action.covered (a : Action) {config : Fin 7 → UnitTriangle}
    (h : Covers 1 config) : Covers 1 (a.transform config) := by
  exact map_cover a.motion a.hexagon _ (covers_reindex config h a.roles.symm)

theorem Action.anchor_mem (a : Action) {config : Fin 7 → UnitTriangle}
    (h : ∀ i, qAnchor 1 i ∈ (config i).region) :
    ∀ i, qAnchor 1 i ∈ (a.transform config i).region := by
  intro i
  rw [Action.transform, map_region]
  refine ⟨qAnchor 1 (a.roles.symm i), h _, ?_⟩
  simp only [a.anchors, Equiv.apply_symm_apply]

theorem Action.nonintruding (a : Action) {config : Fin 7 → UnitTriangle}
    {radius : ℝ} {i : Fin 7} (h : NonIntruding radius (config i)) :
    NonIntruding radius (a.transform config (a.roles i)) := by
  intro p hp
  simp only [Action.transform, Equiv.symm_apply_apply, map_region] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [a.norm]
  exact h q hq

def Action.trans (a b : Action) : Action where
  motion := a.motion.trans b.motion
  roles := a.roles.trans b.roles
  zero := by change b.motion (a.motion 0) = 0; rw [a.zero, b.zero]
  hexagon := by
    change (fun x => b.motion (a.motion x)) '' Hexagon 1 = Hexagon 1
    rw [← Set.image_image (f := a.motion) (g := b.motion), a.hexagon, b.hexagon]
  anchors i := by change b.motion (a.motion (qAnchor 1 i)) = _; rw [a.anchors, b.anchors]; rfl

def identity : Action where
  motion := AffineIsometryEquiv.refl ℝ Plane
  roles := Equiv.refl _
  zero := rfl
  hexagon := Set.image_id _
  anchors _ := rfl

def turnRoles : Equiv.Perm (Fin 7) :=
  Equiv.ofBijective (![1,2,3,4,5,0,6] : Fin 7 → Fin 7) (by decide)

def reflectionRoles : Equiv.Perm (Fin 7) :=
  Equiv.ofBijective (![0,5,4,3,2,1,6] : Fin 7 → Fin 7) (by decide)

def rotationAction : Action where
  motion := turn
  roles := turnRoles
  zero := turn_zero
  hexagon := turn_hexagon 1
  anchors i := by
    fin_cases i
    · exact turn_vertex 1 0
    · exact turn_vertex 1 1
    · exact turn_vertex 1 2
    · exact turn_vertex 1 3
    · exact turn_vertex 1 4
    · exact turn_vertex 1 5
    · exact turn_zero

def reflectionIsometry : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv :=
    { toLinearMap := CornerChart.reflectionLinear
      invFun := CornerChart.reflect
      left_inv := CornerChart.reflect_reflect
      right_inv := CornerChart.reflect_reflect }
  norm_map' := reflect_norm

def reflectionAction : Action where
  motion := reflectionIsometry.toAffineIsometryEquiv
  roles := reflectionRoles
  zero := by change CornerChart.reflect 0 = 0; simp [CornerChart.reflect]
  hexagon := CornerChart.reflection_hexagon
  anchors i := by
    change CornerChart.reflect (qAnchor 1 i) = qAnchor 1 (reflectionRoles i)
    fin_cases i
    · exact CornerChart.reflect_vertex 0
    · exact CornerChart.reflect_vertex 1
    · exact CornerChart.reflect_vertex 2
    · exact CornerChart.reflect_vertex 3
    · exact CornerChart.reflect_vertex 4
    · exact CornerChart.reflect_vertex 5
    · change CornerChart.reflect 0 = 0; simp [CornerChart.reflect]

def rotationPower : Nat → Action
  | 0 => identity
  | n+1 => (rotationPower n).trans rotationAction

def dihedral (n : Fin 6) (flip : Bool) : Action :=
  (rotationPower n.val).trans (if flip then reflectionAction else identity)

theorem pair_reduction (i j : Fin 6) (h : i ≠ j) :
    ∃ n : Fin 6, ∃ flip : Bool, ∃ k : Fin 3,
      (dihedral n flip).roles i.castSucc = (⟨k.val+2, by omega⟩ : Fin 7) ∧
      (dihedral n flip).roles j.castSucc = 5 := by
  revert i j
  decide

/-- Three canonical pair exclusions suffice for all distinct outer NI roles.
The certificate exclusions remain explicit inputs until their full trees close. -/
theorem at_most_one_of_Q_exclusions
    (exclude : ∀ k : Fin 3, ∀ config : Fin 7 → UnitTriangle,
      Covers 1 config → (∀ i, qAnchor 1 i ∈ (config i).region) →
      NonIntruding (1/2) (config ⟨k.val+2, by omega⟩) →
      NonIntruding (1/2) (config 5) → False)
    (config : Fin 7 → UnitTriangle) (covered : Covers 1 config)
    (anchors : ∀ i, qAnchor 1 i ∈ (config i).region)
    (i j : Fin 6) (hi : NonIntruding (1/2) (config i.castSucc))
    (hj : NonIntruding (1/2) (config j.castSucc)) : i = j := by
  by_contra h
  obtain ⟨n, flip, k, hki, h5j⟩ := pair_reduction i j h
  let action := dihedral n flip
  have hi' := action.nonintruding hi
  have hj' := action.nonintruding hj
  change NonIntruding (1/2) (action.transform config ((dihedral n flip).roles i.castSucc)) at hi'
  change NonIntruding (1/2) (action.transform config ((dihedral n flip).roles j.castSucc)) at hj'
  rw [hki] at hi'
  rw [h5j] at hj'
  exact exclude k (action.transform config) (action.covered covered)
    (action.anchor_mem anchors) hi' hj'

end
end HexagonCover.QSymmetry
