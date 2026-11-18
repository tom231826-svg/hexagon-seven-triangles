import HexagonCover.Geometry
import Mathlib.Analysis.Convex.Strict.Extreme

/-!
An independent direct geometric check of the three-point obligation occurring
in frozen Q25 fact 7211. This is not a replay of its 23 interval cells.
-/
namespace HexagonCover

theorem point_eta (z : Plane) : point (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> rfl

namespace UnitTriangle

/-- A diameter-attaining endpoint of a unit triangle is an actual vertex. -/
theorem vertex_of_dist_eq_one (T : UnitTriangle) {x y : Plane}
    (hx : x ∈ T.region) (hy : y ∈ T.region) (hxy : dist x y = 1) :
    ∃ i : Fin 3, T.vertex i = x := by
  have hs : x ∈ Metric.sphere y 1 := hxy
  have he := StrictConvexSpace.sphere_subset_extremePoints_closedBall
    y (by norm_num : (1 : ℝ) ≠ 0) hs
  have hb : T.region ⊆ Metric.closedBall y 1 := fun _ hz => T.dist_le_one hz hy
  have hxext : x ∈ Set.extremePoints ℝ T.region := by
    refine ⟨hx, ?_⟩
    intro u hu v hv huv
    exact he.2 (hb hu) (hb hv) huv
  have hrange : x ∈ Set.range T.vertex :=
    (extremePoints_convexHull_subset (𝕜 := ℝ) (A := Set.range T.vertex)) hxext
  exact hrange

end UnitTriangle

noncomputable def pilotH : ℝ := Real.sqrt 3 / 2
noncomputable def pilotA : Plane := point (-(1 / 2 : ℝ)) pilotH
def pilotB : Plane := point (-1) 0
noncomputable def pilotP : Plane := point (-(1 / 2 : ℝ)) 0

theorem pilotH_pos : 0 < pilotH := by
  unfold pilotH
  positivity

theorem pilotH_sq : pilotH ^ 2 = (3 / 4 : ℝ) := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold pilotH
  nlinarith

theorem pilotAB_distance : dist pilotA pilotB = 1 := by
  have h := dist_point_sq (-(1 / 2 : ℝ)) pilotH (-1) 0
  have hn := dist_nonneg (x := pilotA) (y := pilotB)
  change dist pilotA pilotB ^ 2 = _ at h
  nlinarith [pilotH_sq]

theorem pilot_third_vertex {z : Plane}
    (ha : dist z pilotA = 1) (hb : dist z pilotB = 1) :
    z = 0 ∨ z = point (-(3 / 2 : ℝ)) pilotH := by
  have za : (z 0 + 1 / 2) ^ 2 + (z 1 - pilotH) ^ 2 = 1 := by
    have hh := dist_point_sq (z 0) (z 1) (-(1 / 2 : ℝ)) pilotH
    rw [point_eta] at hh
    change dist z pilotA ^ 2 = _ at hh
    rw [ha] at hh
    nlinarith
  have zb : (z 0 + 1) ^ 2 + z 1 ^ 2 = 1 := by
    have hh := dist_point_sq (z 0) (z 1) (-1) 0
    rw [point_eta] at hh
    change dist z pilotB ^ 2 = _ at hh
    rw [hb] at hh
    nlinarith
  have hlin : z 0 = -2 * pilotH * z 1 := by nlinarith [pilotH_sq]
  have hfactor : z 1 * (z 1 - pilotH) = 0 := by
    rw [hlin] at zb
    have hhprod := congrArg (fun u : ℝ => u * (z 1) ^ 2) pilotH_sq
    nlinarith [hhprod]
  rcases mul_eq_zero.mp hfactor with hz | hz
  · left
    have hx : z 0 = 0 := by rw [hlin, hz]; ring
    rw [← point_eta z, hx, hz, point_zero]
  · right
    have hy : z 1 = pilotH := sub_eq_zero.mp hz
    have hx : z 0 = -(3 / 2 : ℝ) := by rw [hlin, hy]; nlinarith [pilotH_sq]
    rw [← point_eta z, hx, hy]

/-- A real saved NI obligation independently forces the origin into its owner. -/
theorem pilot_origin_forced (T : UnitTriangle)
    (ha : pilotA ∈ T.region) (hb : pilotB ∈ T.region) (hp : pilotP ∈ T.region) :
    (0 : Plane) ∈ T.region := by
  by_contra hzero
  obtain ⟨ia, hia⟩ := T.vertex_of_dist_eq_one ha hb pilotAB_distance
  obtain ⟨ib, hib⟩ := T.vertex_of_dist_eq_one hb ha (by simpa [dist_comm] using pilotAB_distance)
  have hv : ∀ i, 2 * pilotH ≤ (T.vertex i) 1 - 2 * pilotH * (T.vertex i) 0 := by
    intro i
    by_cases hai : T.vertex i = pilotA
    · rw [hai]
      simp only [pilotA, point_coord_zero, point_coord_one]
      linarith
    by_cases hbi : T.vertex i = pilotB
    · rw [hbi]
      simp only [pilotB, point_coord_zero, point_coord_one]
      linarith
    have hia' : i ≠ ia := by intro h; subst i; exact hai hia
    have hib' : i ≠ ib := by intro h; subst i; exact hbi hib
    have hda : dist (T.vertex i) pilotA = 1 := by rw [← hia]; exact T.edgeLength i ia hia'
    have hdb : dist (T.vertex i) pilotB = 1 := by rw [← hib]; exact T.edgeLength i ib hib'
    rcases pilot_third_vertex hda hdb with hz | hz
    · exact False.elim (hzero (hz ▸ T.vertex_mem i))
    · rw [hz]
      simp only [point_coord_zero, point_coord_one]
      nlinarith [pilotH_pos]
  have hc : Convex ℝ {z : Plane | 2 * pilotH ≤ z 1 - 2 * pilotH * z 0} := by
    intro x hx y hy a b ha' hb' hab
    change 2 * pilotH ≤ (a * x 1 + b * y 1) - 2 * pilotH * (a * x 0 + b * y 0)
    calc
      2 * pilotH = a * (2 * pilotH) + b * (2 * pilotH) := by nlinarith [congrArg (fun u : ℝ => u * (2 * pilotH)) hab]
      _ ≤ a * (x 1 - 2 * pilotH * x 0) + b * (y 1 - 2 * pilotH * y 0) :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha') (mul_le_mul_of_nonneg_left hy hb')
      _ = _ := by ring
  have hsub : T.region ⊆ {z : Plane | 2 * pilotH ≤ z 1 - 2 * pilotH * z 0} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact hv i
    · exact hc
  have h := hsub hp
  change 2 * pilotH ≤ (0 : ℝ) - 2 * pilotH * (-(1 / 2 : ℝ)) at h
  nlinarith [pilotH_pos]

theorem pilot_nonintrusion_impossible (T : UnitTriangle)
    (ha : pilotA ∈ T.region) (hb : pilotB ∈ T.region) (hp : pilotP ∈ T.region)
    (hNI : ∀ z ∈ T.region, (1 / 2 : ℝ) ≤ ‖z‖) : False := by
  have h := hNI 0 (pilot_origin_forced T ha hb hp)
  norm_num at h

end HexagonCover
