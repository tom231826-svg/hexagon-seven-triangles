import HexagonCover.GapScalar
import HexagonCover.NoGapChain

/-! The last positive gap gives an endpoint preceding the heavy short reach.
All geometry here uses the same actual normalized seven-piece configuration. -/
namespace HexagonCover.GapScale
open Configuration NormalizedHeavy BoundaryGaps BoundaryOwners
noncomputable section

theorem finite_last_gap : ∀S : Finset (Fin 6), S.Nonempty → 5 ∉ S →
    ∃k : Fin 5, k.castSucc∈S ∧ ∀i : Fin 5,k < i → i.castSucc∉S := by
  decide +kernel

theorem last_gap {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (somegap : ∃i,gap h.cover i) :
    ∃k : Fin 5,gap h.cover k.castSucc ∧
      (∀i : Fin 5,k < i → ¬gap h.cover i.castSucc) := by
  classical
  let S := Finset.univ.filter (gap h.cover)
  have hn : S.Nonempty := by obtain ⟨i,hi⟩:=somegap; exact ⟨i,by simp [S,hi]⟩
  have h5 : (5:Fin 6)∉S := by simpa [S] using edge5_no_gap h
  obtain ⟨k,hk,hl⟩ := finite_last_gap S hn h5
  exact ⟨k,by simpa [S] using hk,fun i hi=>by simpa [S] using hl i hi⟩

theorem last_gap_short_upper {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (k : Fin 5) (last : ∀i : Fin 5,k < i → ¬gap h.cover i.castSucc) :
    a h.cover k.succ  ≤  a h.cover 5 := by
  have step (i : Fin 5) (hi : k < i) : a h.cover i.castSucc  <  a h.cover i.succ := by
    have hl := NoGapChain.light h i
    have hj := le_of_not_gt (last i hi)
    change 1  ≤  b h.cover i.castSucc+a h.cover (i.castSucc+1) at hj
    have he : i.castSucc+1=i.succ := by fin_cases i <;> decide
    rw [he] at hj
    linarith
  fin_cases k
  · exact (step 1 (by decide)).le.trans
      ((step 2 (by decide)).le.trans ((step 3 (by decide)).le.trans (step 4 (by decide)).le))
  · exact (step 2 (by decide)).le.trans ((step 3 (by decide)).le.trans (step 4 (by decide)).le)
  · exact (step 3 (by decide)).le.trans (step 4 (by decide)).le
  · exact (step 4 (by decide)).le
  · exact le_rfl

theorem gap_nine_tenths {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (somegap : ∃i,gap h.cover i) : (9:ℝ)/10  <  M h := by
  have bounds := structure_bounds h
  have hM := HeavyScale.gap_four_fifths h.cover 5 h.heavy5
    (by simpa only [max_eq_M h] using bounds.1) somegap
  rw [max_eq_M h] at hM
  by_contra hn
  have hMhi : M h  ≤  (9:ℝ)/10 := le_of_not_gt hn
  let t := 1-M h
  have ht0 : 0  <  t := by dsimp [t]; linarith [bounds.2.2.2.2.1]
  have ht1 : t  <  1 := by dsimp [t]; linarith
  have disk := CentralDisk.actual_central_disk_of_reach_lower h.cover ht0 ht1 bounds.1
  obtain ⟨k,hk,last⟩ := last_gap h somegap
  have ha := last_gap_short_upper h k last
  have he : k.castSucc+1=k.succ := by fin_cases k <;> decide
  have hab : b h.cover k.castSucc  ≤  1-a h.cover k.succ := by
    change b h.cover k.castSucc+a h.cover (k.castSucc+1) < 1 at hk
    rw [he] at hk
    linarith
  have hp := closed_gap_central h.cover k.castSucc hk
    (1-a h.cover (k.castSucc+1)) ⟨by simpa only [he] using hab,le_rfl⟩
  have hr := CentralRadius.actual_triangle_bound (config 6)
    (CentralDisk.rho_bounds ht0 ht1).1.le disk hp
  rw [GapRadius.edgePoint_norm_sq,he] at hr
  unfold CentralRadius.boundSq at hr
  have hhalf := NoGapChain.a5_lt_half h
  have hproduct : a h.cover k.succ*(1-a h.cover k.succ)  ≤  a h.cover 5*(1-a h.cover 5) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha)
      (show 0  ≤  1-a h.cover k.succ-a h.cover 5 by linarith)]
  have hpoly := ReachEndpoints.actual_exit_constraint h.cover 5
  have hpoly' : (a h.cover 5)^2+(1-t)*a h.cover 5+(1-t)^2  ≤  1 := by
    change (a h.cover 5)^2+a h.cover 5*M h+(M h)^2  ≤  1 at hpoly
    dsimp [t]
    nlinarith only [hpoly]
  have hs := GapScalar.strict_comparison (t:=t) (x:=a h.cover 5)
    (by dsimp [t]; linarith) (by dsimp [t]; linarith)
    (leftReach h.cover 5).positive.le hhalf.le hpoly'
  nlinarith only [hr,hproduct,hs]

theorem normalized_nine_patterns {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (somegap : ∃i,gap h.cover i) :
    ∃S∈ninePatterns,∀i,gap h.cover i ↔ i∈S :=
  positive_gap_nine_patterns h.cover somegap (edge5_no_gap h)

end
end HexagonCover.GapScale
