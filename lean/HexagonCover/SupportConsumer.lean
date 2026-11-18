import HexagonCover.ExactSupport
import HexagonCover.SupportGeometry

/-! Connect the independent all-pair exact checker to actual unit triangles. -/
namespace HexagonCover.SupportConsumer
open DistanceLeaf Quadratic3

theorem eventBase_real (p q : ExactPoint) (role : Fin 3) (negative : Bool) :
    toPlane (ExactSupport.eventBase p q role negative) =
      SupportGeometry.eventBase (toPlane p) (toPlane q) role negative := by
  fin_cases role <;> cases negative <;> ext i <;> fin_cases i <;>
    simp [ExactSupport.eventBase, ExactSupport.perpendicular, ExactSupport.difference,
      ExactSupport.negate, ExactSupport.rotate, ExactSupport.inverseRole,
      SupportGeometry.eventBase, SupportGeometry.signedPerpendicular,
      SupportGeometry.perpendicular, SupportGeometry.inverseRole, SupportGeometry.nvec,
      NICertificate.normalValues, toPlane, ExactSupport.real_halfRoot] <;> ring

theorem dot_rotate_real (base p : ExactPoint) (i : Fin 3) :
    real (ExactSupport.dot (ExactSupport.rotate base i) p) =
      TriangleFrame.dotp (SupportGeometry.nvec (toPlane base 0) (toPlane base 1) i) (toPlane p) := by
  have hc := ExactSupport.rotate_coordinates base i
  have h0 := congrArg Prod.fst hc
  have h1 := congrArg Prod.snd hc
  dsimp only at h0 h1
  rw [ExactSupport.real_dot, h0, h1]
  rfl

theorem total_le_geometric {n : ℕ} (points : Fin (n+1) → ExactPoint) (base : ExactPoint) :
    real (ExactSupport.total points base) ≤
      SupportGeometry.total (fun j => toPlane (points j)) (toPlane base 0) (toPlane base 1) := by
  unfold SupportGeometry.total
  rw [Fin.sum_univ_three]
  apply ExactSupport.total_le points base (fun i => SupportGeometry.support
    (fun j => toPlane (points j)) (toPlane base 0) (toPlane base 1) i)
  intro i j
  rw [dot_rotate_real]
  exact SupportGeometry.dot_le_support (fun j : Fin (n+1) => toPlane (points j))
    (toPlane base 0) (toPlane base 1) i j

/-- Checker acceptance excludes every arbitrary actual unit triangle containing
all checked source points. No fixed orientation, nonintrusion, or hull premise. -/
theorem check_sound {n : ℕ} (points : Fin (n+1) → ExactPoint)
    (accepted : ExactSupport.check points = true) (T : UnitTriangle)
    (contained : ∀ j, toPlane (points j) ∈ T.region) : False := by
  obtain ⟨a, b, hab⟩ := ExactSupport.check_distinct points accepted
  apply SupportGeometry.cannot_contain_of_eventBounds (fun j => toPlane (points j)) hab ?_ T contained
  intro j k hjk role negative
  have h := ExactSupport.eventCheck_sound points (points j) (points k) role negative
    (ExactSupport.check_event points accepted j k hjk role negative)
  have hg := total_le_geometric points (ExactSupport.eventBase (points j) (points k) role negative)
  rw [eventBase_real] at hg
  have hfinal := h.trans_le hg
  simpa only [dist_eq_norm, norm_sub_rev] using hfinal

end HexagonCover.SupportConsumer
