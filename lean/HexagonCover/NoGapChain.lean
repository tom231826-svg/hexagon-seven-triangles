import HexagonCover.NormalizedHeavy
import HexagonCover.ReachEndpoints

/-! Actual no-gap chains and area windows used by the N packet recipe. -/
namespace HexagonCover.NoGapChain
open HexagonCover.Configuration NormalizedHeavy ReachBudget
noncomputable section

theorem light {config : Fin 7 → UnitTriangle} (h : Normalized config) (i : Fin 5) :
    a h.cover i.castSucc+b h.cover i.castSucc < 1 := by
  have hu := (structure_bounds h).2.1
  by_contra hn
  have he := hu i.castSucc (le_of_not_gt hn)
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change i.val=5 at hv
  omega

theorem a_strictMono {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) : StrictMono (a h.cover) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hl := light h i
  have hj := le_of_not_gt (nogaps i.castSucc)
  change 1 ≤ b h.cover i.castSucc+a h.cover (i.castSucc+1) at hj
  have he : i.castSucc+1=i.succ := by fin_cases i <;> decide
  rw [he] at hj
  linarith

theorem b_step {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (i : Fin 5) :
    b h.cover i.castSucc < b h.cover (i.castSucc-1) := by
  have hl := light h i
  have hj := le_of_not_gt (nogaps (i.castSucc-1))
  change 1 ≤ b h.cover (i.castSucc-1)+a h.cover ((i.castSucc-1)+1) at hj
  rw [sub_add_cancel] at hj
  linarith

theorem a5_lt_half {config : Fin 7 → UnitTriangle} (h : Normalized config) :
    a h.cover 5 < (1:ℝ)/2 := by
  have hs := structure_bounds h
  have hM : (2:ℝ)/3 ≤ b h.cover 5 := hs.2.2.2.1.le
  have hc := ReachEndpoints.actual_exit_constraint h.cover 5
  exact ReachEndpoints.short_half_of_long_two_thirds (leftReach h.cover 5).positive.le
    hM (by nlinarith only [hc])

theorem light_reach_order {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) (i : Fin 5) :
    a h.cover i.castSucc < (1:ℝ)/2 ∧ (1:ℝ)/2 < b h.cover i.castSucc := by
  have hm := a_strictMono h nogaps
  have hhalf := a5_lt_half h
  have ha : a h.cover i.castSucc ≤ a h.cover 5 :=
    hm.monotone (by have hh:=i.isLt; change i.val ≤ 5; omega)
  have hb : a h.cover (i.castSucc+1) ≤ a h.cover 5 :=
    hm.monotone (Fin.le_last _)
  have hj := le_of_not_gt (nogaps i.castSucc)
  change 1 ≤ b h.cover i.castSucc+a h.cover (i.castSucc+1) at hj
  constructor <;> linarith

theorem actual_area_window {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (nogaps : ∀i,¬BoundaryGaps.gap h.cover i) :
    (M h)^2+∑i:Fin 5,(a h.cover i.castSucc)^2 ≤ 1 := by
  have hb := cost_budget h.cover
  rw [Fin.sum_univ_castSucc] at hb
  change (∑i:Fin 5,cost h.cover i.castSucc)+cost h.cover 5 ≤ 1 at hb
  have h5 : cost h.cover 5=(M h)^2 := by
    rw [cost,if_pos h.heavy5,max_eq_M h]
  have hi (i : Fin 5) : cost h.cover i.castSucc=(a h.cover i.castSucc)^2 := by
    have hl := light h i
    have ho := light_reach_order h nogaps i
    rw [cost,if_neg (show ¬heavy h.cover i.castSucc from not_le.mpr hl),
      min_eq_left (by linarith : a h.cover i.castSucc ≤ b h.cover i.castSucc)]
  rw [h5] at hb
  simp_rw [hi] at hb
  linarith

end
end HexagonCover.NoGapChain
