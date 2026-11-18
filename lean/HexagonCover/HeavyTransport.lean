import HexagonCover.ReachTransport
import HexagonCover.IntruderReach

/-! The heavy-piece separation and H/D bounds transported to the actual six
outer roles. Rotation preserves the same piece's endpoints, disk and norms. -/
namespace HexagonCover.HeavyTransport
noncomputable section
open HexagonCover.Configuration CornerTransport QSymmetry Symmetry

def cornerAction (i : Fin 6) : Action := inverse (rotationPower i.val)

def rotatedPiece (config : Fin 7 → UnitTriangle) (i : Fin 6) : UnitTriangle :=
  mapTriangle (cornerAction i).motion (config i.castSucc)

theorem rotated_anchor_ball {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    ∃ r>0,Metric.ball ExteriorLoss.corner r⊆(rotatedPiece config i).region := by
  obtain ⟨r,hr,hball⟩ := h.anchorBalls i.castSucc
  rw [qAnchor_outer] at hball
  have hb := action_ball (cornerAction i) (config i.castSucc) (hexVertex 1 i) hball
  change Metric.ball ((inverse (rotationPower i.val)).motion (hexVertex 1 i)) r⊆
    (rotatedPiece config i).region at hb
  rw [inverse_corner] at hb
  exact ⟨r,hr,hb⟩

theorem rotated_endpoints {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    ExteriorLoss.upperEndpoint (b h i)∈(rotatedPiece config i).region ∧
    ExteriorLoss.lowerEndpoint (a h i)∈(rotatedPiece config i).region := by
  constructor
  · rw [rotatedPiece,map_region]
    refine ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) (b h i),
      (rightReach h i).endpoint,?_⟩
    rw [←rotation_upperEndpoint]
    exact (rotationPower i.val).motion.symm_apply_apply _
  · rw [rotatedPiece,map_region]
    refine ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) (a h i),
      (leftReach h i).endpoint,?_⟩
    rw [←rotation_lowerEndpoint]
    exact (rotationPower i.val).motion.symm_apply_apply _

theorem actual_heavy_separation {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hi : 1≤a h i+b h i) :
    ∃D:ℝ,NICertificate.halfRoot*max (a h i) (b h i)≤D ∧
      (1<a h i+b h i → NICertificate.halfRoot*max (a h i) (b h i)<D) ∧
      ∀p∈(config i.castSucc).region,D≤‖p‖ := by
  obtain ⟨r,hr,hball⟩ := rotated_anchor_ball h i
  obtain ⟨hb,ha⟩ := rotated_endpoints h i
  obtain ⟨D,hD,hDs,hP⟩ := HeavyReach.actual_heavy_reach_separation (rotatedPiece config i) (a := b h i) (b := a h i)
    (rightReach h i).positive.le (leftReach h i).positive.le (by linarith) hr hball hb ha
  refine ⟨D,?_,?_,?_⟩
  · simpa only [max_comm (b h i) (a h i)] using hD
  · intro hsum
    simpa only [max_comm (b h i) (a h i)] using hDs (by linarith)
  · exact ReachTransport.pullback_separation (cornerAction i) (config i.castSucc) hP

theorem actual_heavy_strict_half {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hi : 1≤a h i+b h i) :
    ∃D:ℝ,NICertificate.halfRoot/2<D ∧ ∀p∈(config i.castSucc).region,D≤‖p‖ := by
  obtain ⟨r,hr,hball⟩ := rotated_anchor_ball h i
  obtain ⟨hb,ha⟩ := rotated_endpoints h i
  obtain ⟨D,hD,hP⟩ := IntruderReach.actual_heavy_strict_half (rotatedPiece config i) (a := b h i) (b := a h i)
    (rightReach h i).positive.le (leftReach h i).positive.le (by linarith) hr hball hb ha
  exact ⟨D,hD,ReachTransport.pullback_separation (cornerAction i) (config i.castSucc) hP⟩

/-- A heavy piece whose maximum actual reach exceeds 1/sqrt3 is nonintruding
in the exact same physical radius-1/2 sense used by the Q consumers. -/
theorem actual_heavy_nonintruding {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) (hi : 1≤a h i+b h i)
    (hmax : IntruderReach.q < max (a h i) (b h i)) :
    NonIntruding (1/2) (config i.castSucc) := by
  obtain ⟨D,hD,_,hP⟩ := actual_heavy_separation h i hi
  have hm := mul_lt_mul_of_pos_left hmax ExtremeTriangle.halfRoot_pos
  rw [IntruderReach.halfRoot_q] at hm
  intro p hp
  exact (hm.trans_le (hD.trans (hP p hp))).le

theorem q_eq_sqrt_div_three : IntruderReach.q=Real.sqrt 3/3 := by
  unfold IntruderReach.q
  apply (div_eq_div_iff (by positivity) (by norm_num)).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

end
end HexagonCover.HeavyTransport
