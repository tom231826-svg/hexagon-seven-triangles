import HexagonCover.QSymmetry
import HexagonCover.ClippedCornerArea
import HexagonCover.AreaCorollaries

/-! Transport real exterior losses of the same actual piece to any corner.
No replacement configuration is used for combining area and reach conditions. -/
namespace HexagonCover.CornerTransport
open QSymmetry Symmetry MeasureTheory
noncomputable section

theorem linear_eq_motion (a : Action) (p : Plane) :
    a.motion.linearIsometryEquiv p = a.motion p := by
  simpa only [vsub_eq_sub, sub_zero, a.zero] using a.motion.map_vsub p 0

theorem action_area (a : Action) (s : Set Plane) :
    volume.real (a.motion '' s) = volume.real s := by
  let f := a.motion.linearIsometryEquiv
  have h := f.measurePreserving.measure_preimage_emb
    f.toHomeomorph.measurableEmbedding (f '' s)
  rw [Set.preimage_image_eq _ f.injective] at h
  have hf : (f : Plane → Plane) = a.motion := funext (linear_eq_motion a)
  rw [hf] at h
  exact congrArg ENNReal.toReal h.symm

theorem action_exterior_area (a : Action) (T : UnitTriangle) :
    volume.real ((mapTriangle a.motion T).region \ Hexagon 1) =
      volume.real (T.region \ Hexagon 1) := by
  rw [map_region]
  have h := Set.image_sdiff a.motion.injective T.region (Hexagon 1)
  rw [a.hexagon] at h
  rw [← h, action_area]

def inverse (a : Action) : Action where
  motion := a.motion.symm
  roles := a.roles.symm
  zero := by
    apply a.motion.injective
    rw [a.motion.apply_symm_apply, a.zero]
  hexagon := by
    calc
      a.motion.symm '' Hexagon 1 = a.motion.symm '' (a.motion '' Hexagon 1) :=
        congrArg (fun s => a.motion.symm '' s) a.hexagon.symm
      _ = Hexagon 1 := by
        ext p
        simp only [Set.mem_image]
        constructor
        · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
          simpa using hq
        · intro hp
          exact ⟨a.motion p, ⟨p, hp, rfl⟩, a.motion.symm_apply_apply p⟩
  anchors i := by
    apply a.motion.injective
    rw [a.motion.apply_symm_apply, a.anchors, Equiv.apply_symm_apply]

theorem action_ball (a : Action) (T : UnitTriangle) (u : Plane) {r : ℝ}
    (h : Metric.ball u r ⊆ T.region) :
    Metric.ball (a.motion u) r ⊆ (mapTriangle a.motion T).region := by
  intro p hp
  rw [map_region]
  refine ⟨a.motion.symm p, h ?_, a.motion.apply_symm_apply p⟩
  change dist (a.motion.symm p) u < r
  have hd := a.motion.isometry.dist_eq (a.motion.symm p) u
  rw [a.motion.apply_symm_apply] at hd
  exact hd ▸ hp

theorem action_lineMap (a : Action) (u v : Plane) (t : ℝ) :
    a.motion (AffineMap.lineMap u v t) =
      AffineMap.lineMap (a.motion u) (a.motion v) t :=
  a.motion.toAffineIsometry.toAffineMap.apply_lineMap u v t

theorem rotationPower_vertex (i j : Fin 6) :
    (rotationPower i.val).motion (hexVertex 1 j) = hexVertex 1 (j + i) := by
  fin_cases i
  all_goals simp only [rotationPower, Action.trans, rotationAction, identity,
    AffineIsometryEquiv.coe_trans, AffineIsometryEquiv.coe_refl, Function.comp_apply,
    id_eq, turn_vertex]
  all_goals try congr 1
  all_goals fin_cases j <;> decide

theorem rotation_corner (i : Fin 6) :
    (rotationPower i.val).motion ExteriorLoss.corner = hexVertex 1 i := by
  have h := rotationPower_vertex i 0
  simpa [ExteriorLoss.corner, hexVertex] using h

theorem inverse_corner (i : Fin 6) :
    (inverse (rotationPower i.val)).motion (hexVertex 1 i) = ExteriorLoss.corner := by
  rw [← rotation_corner i]
  exact (rotationPower i.val).motion.symm_apply_apply _

theorem upperEndpoint_eq_lineMap (t : ℝ) :
    ExteriorLoss.upperEndpoint t = AffineMap.lineMap (hexVertex 1 0) (hexVertex 1 1) t := by
  ext i
  fin_cases i <;> simp [ExteriorLoss.upperEndpoint, ExteriorLoss.corner, ExteriorLoss.upperRay,
    NICertificate.halfRoot, hexVertex, AffineMap.lineMap_apply] <;> ring

theorem lowerEndpoint_eq_lineMap (t : ℝ) :
    ExteriorLoss.lowerEndpoint t = AffineMap.lineMap (hexVertex 1 0) (hexVertex 1 5) t := by
  ext i
  fin_cases i <;> simp [ExteriorLoss.lowerEndpoint, ExteriorLoss.corner, ExteriorLoss.lowerRay,
    NICertificate.halfRoot, hexVertex, AffineMap.lineMap_apply] <;> ring

theorem rotation_upperEndpoint (i : Fin 6) (t : ℝ) :
    (rotationPower i.val).motion (ExteriorLoss.upperEndpoint t) =
      AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t := by
  rw [upperEndpoint_eq_lineMap]
  rw [action_lineMap]
  simp only [rotationPower_vertex]
  congr 1 <;> congr 1 <;> simp [add_comm]

theorem rotation_lowerEndpoint (i : Fin 6) (t : ℝ) :
    (rotationPower i.val).motion (ExteriorLoss.lowerEndpoint t) =
      AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) t := by
  rw [lowerEndpoint_eq_lineMap]
  rw [action_lineMap]
  simp only [rotationPower_vertex]
  have h0 : (0 : Fin 6) + i = i := zero_add i
  have h5 : (5 : Fin 6) + i = i-1 := by fin_cases i <;> decide
  rw [h0, h5]

theorem actual_corner_loss_at (i : Fin 6) (T : UnitTriangle) {a b r : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hr : 0 < r) (ball : Metric.ball (hexVertex 1 i) r ⊆ T.region)
    (left : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) a ∈ T.region)
    (right : AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) b ∈ T.region) :
    AreaCorollaries.delta * (min a b)^2 ≤ volume.real (T.region \ Hexagon 1) ∧
      (1 ≤ a+b → AreaCorollaries.delta * (max a b)^2 ≤ volume.real (T.region \ Hexagon 1)) := by
  let action := inverse (rotationPower i.val)
  let rotated := mapTriangle action.motion T
  have ball' := action_ball action T (hexVertex 1 i) ball
  change Metric.ball ((inverse (rotationPower i.val)).motion (hexVertex 1 i)) r ⊆
    rotated.region at ball'
  rw [inverse_corner] at ball'
  have upper : ExteriorLoss.upperEndpoint b ∈ rotated.region := by
    rw [map_region]
    refine ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) b, right, ?_⟩
    rw [← rotation_upperEndpoint]
    exact (rotationPower i.val).motion.symm_apply_apply _
  have lower : ExteriorLoss.lowerEndpoint a ∈ rotated.region := by
    rw [map_region]
    refine ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) a, left, ?_⟩
    rw [← rotation_lowerEndpoint]
    exact (rotationPower i.val).motion.symm_apply_apply _
  have h := ClippedCornerArea.actual_corner_loss_bounds rotated hb0 hb1 ha0 ha1
    hr ball' upper lower
  have harea : volume.real (rotated.region \ Hexagon 1) = volume.real (T.region \ Hexagon 1) :=
    action_exterior_area action T
  rw [harea] at h
  simpa only [min_comm b a, max_comm b a, add_comm b a,
    AreaCorollaries.delta, ClippedCornerArea.delta] using h

theorem actual_reach_loss {config : Fin 7 → UnitTriangle}
    (h : Configuration.StrictCover config) (i : Fin 6) :
    AreaCorollaries.delta * (min (Configuration.a h i) (Configuration.b h i))^2 ≤
      volume.real ((config i.castSucc).region \ Hexagon 1) ∧
    (1 ≤ Configuration.a h i + Configuration.b h i →
      AreaCorollaries.delta * (max (Configuration.a h i) (Configuration.b h i))^2 ≤
        volume.real ((config i.castSucc).region \ Hexagon 1)) := by
  obtain ⟨r, hr, hb⟩ := h.anchorBalls i.castSucc
  rw [Configuration.qAnchor_outer] at hb
  exact actual_corner_loss_at i (config i.castSucc)
    (Configuration.leftReach h i).positive (Configuration.leftReach h i).lt_one.le
    (Configuration.rightReach h i).positive (Configuration.rightReach h i).lt_one.le
    hr hb (Configuration.leftReach h i).endpoint (Configuration.rightReach h i).endpoint

theorem min_reach_square_sum_le_one {config : Fin 7 → UnitTriangle}
    (h : Configuration.StrictCover config) :
    ∑ i : Fin 6, (min (Configuration.a h i) (Configuration.b h i))^2 ≤ 1 := by
  have hb := AreaCorollaries.unit_cover_exterior_budget config h.covered
  rw [Fin.sum_univ_castSucc] at hb
  change (∑ i : Fin 6, AreaBudget.area ((config i.castSucc).region \ Hexagon 1)) +
    AreaBudget.area ((config 6).region \ Hexagon 1) ≤ AreaCorollaries.delta at hb
  have hc : 0 ≤ AreaBudget.area ((config 6).region \ Hexagon 1) := ENNReal.toReal_nonneg
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin 6) _ => (actual_reach_loss h i).1)
  rw [← Finset.mul_sum] at hs
  have hmul : AreaCorollaries.delta *
      (∑ i : Fin 6, (min (Configuration.a h i) (Configuration.b h i))^2) ≤
      AreaCorollaries.delta * 1 := by
    change _ ≤ AreaBudget.area _ at hc
    change _ + _ ≤ _ at hb
    change _ ≤ ∑ i : Fin 6, AreaBudget.area ((config i.castSucc).region \ Hexagon 1) at hs
    linarith
  exact (mul_le_mul_iff_right₀ AreaCorollaries.delta_pos).mp hmul

end
end HexagonCover.CornerTransport
