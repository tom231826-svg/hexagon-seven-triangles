import HexagonCover.GlobalMinimum

/-! Exact scale bounds from the unique heavy piece, valid for the same actual
configuration. The two-thirds bound below does not presuppose absence of gaps. -/
namespace HexagonCover.HeavyScale
open Configuration ReachBudget GlobalMinimum
open scoped Classical
noncomputable section

theorem distant_min_strict {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    (j k : Fin 6) (unique : ∀ i, heavy h i → i=j)
    (lower : ∀ i, 1-max (a h j) (b h j) ≤ min (a h i) (b h i))
    (hn : j ≠ k-1  ∧  j ≠ k+1) :
    1-max (a h j) (b h j)  <  min (a h k) (b h k) := by
  by_contra hnot
  have he : min (a h k) (b h k)=1-max (a h j) (b h j) :=
    le_antisymm (le_of_not_gt hnot) (lower k)
  have hl : ∀ i, min (a h k) (b h k) ≤ min (a h i) (b h i) := by
    intro i
    rw [he]
    exact lower i
  obtain ⟨l,hadj,_,hl,_⟩ := adjacent_heavy h k hl
  rw [unique l hl] at hadj
  exact hadj.elim hn.1 hn.2

theorem two_thirds {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    (j : Fin 6) (hj : heavy h j)
    (lower : ∀ i, 1-max (a h j) (b h j) ≤ min (a h i) (b h i))
    (unique : ∀ i, heavy h i → i=j) : (2:ℝ)/3  <  max (a h j) (b h j) := by
  let M := max (a h j) (b h j)
  let t := 1-M
  let k : Fin 6 := j+3
  have hMt : M < 1 := max_lt (leftReach h j).lt_one (rightReach h j).lt_one
  have ht : 0 < t := by dsimp [t]; linarith
  have hkj : k ≠ j := by dsimp [k]; fin_cases j <;> decide
  have hstrict : t  <  min (a h k) (b h k) :=
    distant_min_strict h j k unique lower (by dsimp [k]; fin_cases j <;> decide)
  let base (i : Fin 6) : ℝ := t^2+(if i=j then M^2-t^2 else 0)
  have hle (i : Fin 6) : base i ≤ cost h i := by
    by_cases hi : i=j
    · subst i
      simp only [base,eq_self,ite_true,cost,if_pos hj]
      dsimp only [M]
      linarith
    · simp only [base,if_neg hi,add_zero]
      exact (pow_le_pow_left₀ ht.le (lower i) 2).trans (min_square_le_cost h i)
  have hk : base k < cost h k := by
    simp only [base,if_neg hkj,add_zero]
    have hs : t^2 < (min (a h k) (b h k))^2 := by
      nlinarith [min_pos h k]
    exact hs.trans_le (min_square_le_cost h k)
  have hs := Finset.sum_lt_sum (s:=Finset.univ) (fun i _=>hle i)
    ⟨k,Finset.mem_univ k,hk⟩
  have he : (∑ i : Fin 6,base i)=M^2+5*t^2 := by
    simp [base,Finset.sum_add_distrib]
    ring
  rw [he] at hs
  have hb := cost_budget h
  have hprod : (3*M-2)*(M-1) < 0 := by dsimp only [t] at hs; nlinarith
  have hm : 0 < 3*M-2 := by
    by_contra hn
    have hp := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hn) (by linarith : M-1 ≤ 0)
    linarith
  change (2:ℝ)/3 < M
  linarith

theorem gap_four_fifths {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    (j : Fin 6) (hj : heavy h j)
    (lower : ∀ i, 1-max (a h j) (b h j) ≤ min (a h i) (b h i))
    (gap : ∃ i, BoundaryGaps.gap h i) : (4:ℝ)/5  <  max (a h j) (b h j) := by
  let M := max (a h j) (b h j)
  let t := 1-M
  have hM0 : 1/2 ≤ M := heavy_max_half h j hj
  have hM1 : M < 1 := max_lt (leftReach h j).lt_one (rightReach h j).lt_one
  have ht0 : 0 < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have disk := CentralDisk.actual_central_disk_of_reach_lower h ht0 ht1 lower
  obtain ⟨i,hi⟩ := gap
  have hs := GapRadius.gap_small h (CentralDisk.rho_bounds ht0 ht1).1.le disk i hi
  have hr := IntruderReach.rmax_half_lt_two_twentyfive
  have hsafe := IntruderReach.rho_gt_safe_radius ht0 ht1
  by_contra hn
  change ¬(4:ℝ)/5 < M at hn
  have htlow : 1/5 ≤ t := by dsimp [t]; linarith
  have hthigh : t ≤ 1/2 := by dsimp [t]; linarith
  have hp := mul_nonneg (sub_nonneg.mpr htlow) (show 0 ≤ 4/5-t by linarith)
  nlinarith

end
end HexagonCover.HeavyScale
