import HexagonCover.Controls
import HexagonCover.GenericNI
import HexagonCover.ExactSupport

/-! Boundary controls against actual feasible triangles. In particular no
certificate can make the sound NI checker reject the explicit tangent triangle
at squared radius 1/4. -/
namespace HexagonCover.SemanticControls
open DistanceLeaf

def standardPoints : Fin 3 → ExactPoint :=
  ![fromXYZ 0 0 0, fromXYZ 1 0 0, fromXYZ (1/2) 0 (1/2)]

theorem unit_support_not_rejected : ExactSupport.check (n := 2) standardPoints = false := by
  decide +kernel

def tangentPoints : Fin 3 → ExactPoint :=
  ![fromXYZ (-(1/2)) (1/2) 0, fromXYZ (1/2) (1/2) 0, fromXYZ 0 (1/2) (1/2)]

theorem tangent_points_real (i : Fin 3) :
    toPlane (tangentPoints i) = Controls.tangentTriangle.vertex i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [tangentPoints, Controls.tangentTriangle, Controls.tangentVertices,
      toPlane, fromXYZ, Quadratic3.real, Quadratic3.ofRat, pilotH, point] <;> ring

theorem tangent_points_contained : ∀ p ∈ List.ofFn tangentPoints,
    toPlane p ∈ Controls.tangentTriangle.region := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  rw [tangent_points_real]
  exact Controls.tangentTriangle.vertex_mem i

/-- Universal control: arbitrary direction cells, weights or annotations cannot
produce an accepted exclusion of this actual tangent, nonintruding triangle. -/
theorem tangent_certificate_rejected (certificate : GenericNI.Certificate) :
    GenericNI.check (List.ofFn tangentPoints) (1/4) certificate = false := by
  cases hc : GenericNI.check (List.ofFn tangentPoints) (1/4) certificate with
  | false => rfl
  | true =>
      exfalso
      apply GenericNI.nonintrusion_impossible hc Controls.tangentTriangle tangent_points_contained
      intro p hp
      have h := Controls.tangent_nonintrusion p hp
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
      nlinarith [norm_nonneg p]

end HexagonCover.SemanticControls
