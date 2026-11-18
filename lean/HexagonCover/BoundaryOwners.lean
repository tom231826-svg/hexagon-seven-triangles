import HexagonCover.Configuration
import HexagonCover.TriangleFrame

/-! Every closed boundary edge is covered only by its two adjacent outer
pieces and the same central piece. Strict anchor balls exclude equality cases. -/
namespace HexagonCover.BoundaryOwners
open HexagonCover.Configuration
noncomputable section

def edgePoint (i : Fin 6) (t : ℝ) : Plane :=
  AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t

theorem edgePoint_mem (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    edgePoint i t ∈ Hexagon 1 := by
  apply (convex_hexagon 1).segment_subset
    (subset_convexHull ℝ _ ⟨i, rfl⟩) (subset_convexHull ℝ _ ⟨i+1, rfl⟩)
  rw [segment_eq_image_lineMap]
  exact ⟨t, ht, rfl⟩

theorem other_anchor_distance (i j : Fin 6) (hji : j ≠ i) (hjn : j ≠ i+1)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    1 ≤ dist (hexVertex 1 j) (edgePoint i t) := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hsq := TriangleFrame.dist_sq_coordinates (hexVertex 1 j) (edgePoint i t)
  have hsqrt := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hnonneg := dist_nonneg (x := hexVertex 1 j) (y := edgePoint i t)
  generalize hd : dist (hexVertex 1 j) (edgePoint i t) = z at hsq hnonneg ⊢
  fin_cases i <;> fin_cases j
  all_goals try exact (hji rfl).elim
  all_goals try exact (hjn rfl).elim
  all_goals
    norm_num [edgePoint, hexVertex, AffineMap.lineMap_apply, point] at hsq hnonneg ⊢
    ring_nf at hsq
    simp only [hsqrt] at hsq
    nlinarith [sq_nonneg t, sq_nonneg (1-t)]

theorem only_adjacent_or_center {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    {j : Fin 7} (hp : edgePoint i t ∈ (config j).region) :
    j = i.castSucc ∨ j = (i+1).castSucc ∨ j = 6 := by
  by_cases hj6 : j = 6
  · exact Or.inr (Or.inr hj6)
  have hjlt : j.val < 6 := by omega
  let k : Fin 6 := ⟨j.val, hjlt⟩
  have hkj : k.castSucc = j := by ext; rfl
  by_cases hki : k = i
  · exact Or.inl (hkj.symm.trans (congrArg Fin.castSucc hki))
  by_cases hkn : k = i+1
  · exact Or.inr (Or.inl (hkj.symm.trans (congrArg Fin.castSucc hkn)))
  have hd := other_anchor_distance i k hki hkn ht
  obtain ⟨r, hr, hb⟩ := h.anchorBalls k.castSucc
  rw [qAnchor_outer] at hb
  have hlt := dist_from_strict_anchor_lt_one (config k.castSucc) _ hr hb
    (edgePoint i t) (by simpa only [hkj] using hp)
  linarith

theorem actual_three_owners {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    edgePoint i t ∈ (config i.castSucc).region ∨
    edgePoint i t ∈ (config (i+1).castSucc).region ∨
    edgePoint i t ∈ (config 6).region := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h.covered (edgePoint_mem i ht))
  rcases only_adjacent_or_center h i ht hj with rfl | rfl | rfl
  · exact Or.inl hj
  · exact Or.inr (Or.inl hj)
  · exact Or.inr (Or.inr hj)

end
end HexagonCover.BoundaryOwners
