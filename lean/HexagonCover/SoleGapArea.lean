import HexagonCover.GapChains
import HexagonCover.GapScaleSharp

/-! Actual same-configuration reach order and area window when edge4 is the
only positive gap. This gives the b0>4/5 duty without an A-in-T2 assumption. -/
namespace HexagonCover.SoleGapArea
noncomputable section
open HexagonCover.Configuration NormalizedHeavy BoundaryGaps ReachBudget

theorem no_prefix_gap {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) (i : Fin 4) : ¬gap h.cover i.castSucc.castSucc := by
  intro hg
  have he := congrArg Fin.val ((sole _).mp hg)
  change i.val=4 at he
  have hi := i.isLt
  omega

theorem a_strictMono {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) :
    StrictMono (fun i:Fin 5 => a h.cover i.castSucc) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hl := NoGapChain.light h i.castSucc
  have hj := le_of_not_gt (no_prefix_gap h sole i)
  change 1 ≤ b h.cover i.castSucc.castSucc+a h.cover (i.castSucc.castSucc+1) at hj
  have he : i.castSucc.castSucc+1=i.succ.castSucc := by fin_cases i <;> decide
  rw [he] at hj
  linarith

theorem b_step {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) (i : Fin 4) :
    b h.cover i.succ.castSucc < b h.cover i.castSucc.castSucc := by
  have hl := NoGapChain.light h i.succ
  have hj := le_of_not_gt (no_prefix_gap h sole i)
  change 1 ≤ b h.cover i.castSucc.castSucc+a h.cover (i.castSucc.castSucc+1) at hj
  have he : i.castSucc.castSucc+1=i.succ.castSucc := by fin_cases i <;> decide
  rw [he] at hj
  linarith

theorem b4_half {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) : 1/2 < b h.cover 4 := by
  have hg := (sole 4).mpr rfl
  have hwidth := GapChains.gap_width h 4 hg
  have hM := GapScale.gap_nine_tenths h ⟨4,hg⟩
  have hM1 := (structure_bounds h).2.2.2.2.1
  have hrad := GapChains.trace_sqrt_gt_two (t:=1-M h) (by linarith) (by linarith)
  have hshort := GapChains.heavy_short h
  change 1/2+Real.sqrt (8*NICertificate.halfRoot*CommonReach.rho (1-M h)/3) ≤
    b h.cover 4+a h.cover 5 at hwidth
  linarith

theorem light_reach_order {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) (i : Fin 5) :
    a h.cover i.castSucc < 1/2 ∧ 1/2 < b h.cover i.castSucc := by
  have h01 := b_step h sole 0
  have h12 := b_step h sole 1
  have h23 := b_step h sole 2
  have h34 := b_step h sole 3
  have h4 := b4_half h sole
  change b h.cover 1 < b h.cover 0 at h01
  change b h.cover 2 < b h.cover 1 at h12
  change b h.cover 3 < b h.cover 2 at h23
  change b h.cover 4 < b h.cover 3 at h34
  have hb : 1/2 < b h.cover i.castSucc := by
    fin_cases i
    · change 1/2 < b h.cover 0; linarith
    · change 1/2 < b h.cover 1; linarith
    · change 1/2 < b h.cover 2; linarith
    · change 1/2 < b h.cover 3; linarith
    · change 1/2 < b h.cover 4; exact h4
  have hl := NoGapChain.light h i
  exact ⟨by linarith,hb⟩

/-- The actual Lebesgue exterior-loss budget yields the source's sole-gap window. -/
theorem actual_area_window {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) :
    (M h)^2+∑i:Fin 5,(a h.cover i.castSucc)^2 ≤ 1 := by
  have hb := cost_budget h.cover
  rw [Fin.sum_univ_castSucc] at hb
  change (∑i:Fin 5,cost h.cover i.castSucc)+cost h.cover 5 ≤ 1 at hb
  have h5 : cost h.cover 5=(M h)^2 := by rw [cost,if_pos h.heavy5,max_eq_M h]
  have hi (i : Fin 5) : cost h.cover i.castSucc=(a h.cover i.castSucc)^2 := by
    have hl := NoGapChain.light h i
    have ho := light_reach_order h sole i
    rw [cost,if_neg (show ¬heavy h.cover i.castSucc from not_le.mpr hl),
      min_eq_left (by linarith : a h.cover i.castSucc ≤ b h.cover i.castSucc)]
  rw [h5] at hb
  simp_rw [hi] at hb
  linarith

theorem four_a1_budget {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) :
    (M h)^2+4*(a h.cover 1)^2 ≤ 1 := by
  have hm := (a_strictMono h sole).monotone
  have hbound : ∀i:Fin 4,(a h.cover 1)^2 ≤ (a h.cover i.succ.castSucc)^2 := by
    intro i
    apply pow_le_pow_left₀ (show 0 ≤ a h.cover 1 from (leftReach h.cover 1).positive.le)
    exact hm (show (1:Fin 5) ≤ i.succ by change 1 ≤ i.val+1; omega)
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (i:Fin 4) _ => hbound i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have ha := actual_area_window h sole
  rw [Fin.sum_univ_succ] at ha
  change (M h)^2+((a h.cover 0)^2+∑i:Fin 4,(a h.cover i.succ.castSucc)^2) ≤ 1 at ha
  nlinarith only [ha,hs,sq_nonneg (a h.cover 0)]

theorem a1_fifth {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) : a h.cover 1 < 1/5 := by
  have hM := GapScaleSharp.gap_twenty_three_twenty_fifths h ⟨4,(sole 4).mpr rfl⟩
  have hM0 : 0 ≤ M h := by linarith
  have hMsq := (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 23/25) hM0).mpr hM
  have hb := four_a1_budget h sole
  by_contra hn
  have hsq := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1/5)
    (leftReach h.cover 1).positive.le).mpr (le_of_not_gt hn)
  change (1/5:ℝ)^2 ≤ (a h.cover 1)^2 at hsq
  nlinarith only [hMsq,hb,hsq]

theorem b0_four_fifths {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (sole : ∀i,gap h.cover i ↔ i=4) : 4/5 < b h.cover 0 := by
  have ha := a1_fifth h sole
  have hj := le_of_not_gt (no_prefix_gap h sole 0)
  change 1 ≤ b h.cover 0+a h.cover 1 at hj
  linarith

end
end HexagonCover.SoleGapArea
