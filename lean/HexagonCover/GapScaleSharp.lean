import HexagonCover.GapScale
import HexagonCover.GapScalarSharp

/-! Closed-interval sharpening, with the same actual gap endpoint and C. -/
namespace HexagonCover.GapScaleSharp
open Configuration NormalizedHeavy BoundaryGaps BoundaryOwners
noncomputable section

theorem gap_twenty_three_twenty_fifths {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (somegap : ∃i,gap h.cover i) : (23:ℝ)/25  <  M h := by
  have bounds := structure_bounds h
  have hM := GapScale.gap_nine_tenths h somegap
  by_contra hn
  have hMhi : M h  ≤  (23:ℝ)/25 := le_of_not_gt hn
  let t := 1-M h
  have ht0 : 0  <  t := by dsimp [t]; linarith [bounds.2.2.2.2.1]
  have ht1 : t  <  1 := by dsimp [t]; linarith
  have disk := CentralDisk.actual_central_disk_of_reach_lower h.cover ht0 ht1 bounds.1
  obtain ⟨k,hk,last⟩ := GapScale.last_gap h somegap
  have ha := GapScale.last_gap_short_upper h k last
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
  have hs := GapScalarSharp.strict_comparison (t:=t) (x:=a h.cover 5)
    (by dsimp [t]; linarith) (by dsimp [t]; linarith)
    (leftReach h.cover 5).positive.le hhalf.le hpoly'
  nlinarith only [hr,hproduct,hs]

end
end HexagonCover.GapScaleSharp
