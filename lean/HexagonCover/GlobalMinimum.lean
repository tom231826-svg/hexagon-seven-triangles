import HexagonCover.GapRadius
import HexagonCover.ReachBudget

/-! Source-exposed alternative to the walking argument: an attained global
minimum of the twelve actual reaches cannot border a positive gap. Its adjacent
outer piece is heavy, and the same minimum supplies the universal reach bound.
No Q certificate exclusion is a premise of these results. -/
namespace HexagonCover.GlobalMinimum
open Configuration BoundaryGaps ReachBudget
noncomputable section

theorem adjacent_heavy {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    (k : Fin 6) (lower : ∀ i, min (a h k) (b h k)  ≤  min (a h i) (b h i)) :
    ∃ j,  (j=k-1  ∨  j=k+1)  ∧  j ≠ k  ∧  heavy h j  ∧ 
      1-min (a h k) (b h k)  ≤  max (a h j) (b h j) := by
  let m := min (a h k) (b h k)
  have hm0 : 0 < m := min_pos h k
  have hm1 : m < 1 := (min_le_left _ _).trans_lt (leftReach h k).lt_one
  have ha (i : Fin 6) : m ≤ a h i := (lower i).trans (min_le_left _ _)
  have hb (i : Fin 6) : m ≤ b h i := (lower i).trans (min_le_right _ _)
  by_cases hak : a h k ≤ b h k
  · have he : a h k=m := (min_eq_left hak).symm
    have hn := GapRadius.minimum_not_gap h hm0 hm1 lower (k-1)
      (Or.inr (by simpa only [sub_add_cancel] using he))
    have hg := le_of_not_gt hn
    change 1  ≤  b h (k-1)+a h ((k-1)+1) at hg
    rw [sub_add_cancel,he] at hg
    refine ⟨k-1,Or.inl rfl,by fin_cases k <;> decide,?_,?_⟩
    · change 1 ≤ a h (k-1)+b h (k-1)
      linarith [ha (k-1)]
    · linarith [le_max_right (a h (k-1)) (b h (k-1))]
  · have he : b h k=m := (min_eq_right (le_of_not_ge hak)).symm
    have hn := GapRadius.minimum_not_gap h hm0 hm1 lower k (Or.inl he)
    have hg := le_of_not_gt hn
    change 1  ≤  b h k+a h (k+1) at hg
    rw [he] at hg
    refine ⟨k+1,Or.inr rfl,by fin_cases k <;> decide,?_,?_⟩
    · change 1 ≤ a h (k+1)+b h (k+1)
      linarith [hb (k+1)]
    · linarith [le_max_left (a h (k+1)) (b h (k+1))]

theorem minimum_lt_one_minus_q {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    (k : Fin 6) (lower : ∀ i, min (a h k) (b h k)  ≤  min (a h i) (b h i)) :
    min (a h k) (b h k) < 1-Real.sqrt 3/3 := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (i:Fin 6) _ =>
    pow_le_pow_left₀ (min_pos h k).le (lower i) 2)
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hb := CornerTransport.min_reach_square_sum_le_one h
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hr0 := Real.sqrt_nonneg (3:ℝ)
  have hr7 : Real.sqrt (3:ℝ) < 7/4 := by nlinarith
  have hq : 0 ≤ 1-Real.sqrt 3/3 := by linarith
  by_contra hn
  have he := pow_le_pow_left₀ hq (le_of_not_gt hn) 2
  nlinarith

/-- Unconditional actual existence and uniqueness of the heavy outer piece,
with the universal lower bound needed later. This is still not the full covering
contradiction, and does not assert that all other outer pieces are intruding. -/
theorem exists_unique_heavy {config : Fin 7  →  UnitTriangle} (h : StrictCover config) :
    ∃ j,  heavy h j  ∧ 
      (∀ i, 1-max (a h j) (b h j) ≤ min (a h i) (b h i))  ∧ 
      Real.sqrt 3/3  <  max (a h j) (b h j)  ∧ 
      ∀ k, heavy h k → k=j := by
  obtain ⟨k,_,hk⟩ := Finset.exists_min_image Finset.univ
    (fun i:Fin 6=>min (a h i) (b h i)) Finset.univ_nonempty
  have lower : ∀ i, min (a h k) (b h k) ≤ min (a h i) (b h i) :=
    fun i=>hk i (Finset.mem_univ i)
  obtain ⟨j,_,_,hj,hM⟩ := adjacent_heavy h k lower
  have hl : ∀ i, 1-max (a h j) (b h j) ≤ min (a h i) (b h i) := by
    intro i
    linarith [lower i]
  have hm := minimum_lt_one_minus_q h k lower
  exact ⟨j,hj,hl,by linarith,unique_heavy_of_reach_lower h j hj hl⟩

/-- Equality in the heavy reach sum would force a second heavy neighbor. -/
theorem heavy_sum_gt_one {config : Fin 7  →  UnitTriangle} (h : StrictCover config)
    (j : Fin 6) (hj : heavy h j)
    (lower : ∀ i, 1-max (a h j) (b h j) ≤ min (a h i) (b h i))
    (unique : ∀ k, heavy h k → k=j) : 1 < a h j+b h j := by
  by_contra hn
  have he : a h j+b h j=1 := by
    change 1 ≤ a h j+b h j at hj
    linarith
  have hsum := min_add_max (a h j) (b h j)
  have hl : ∀ i, min (a h j) (b h j) ≤ min (a h i) (b h i) := by
    intro i
    linarith [lower i]
  obtain ⟨k,_,hkj,hk,_⟩ := adjacent_heavy h j hl
  exact hkj (unique k hk)

end
end HexagonCover.GlobalMinimum
