import HexagonCover.BoundaryOwners

/-! Boundary contacts of the same central triangle. Endpoint equality is
retained in the contact definition and then excluded by the strict center ball. -/
namespace HexagonCover.CentralBoundary
open BoundaryOwners HexagonCover.Configuration
noncomputable section

theorem vertex_not_central {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) : hexVertex 1 i ∉ (config 6).region := by
  obtain ⟨r, hr, hb⟩ := h.anchorBalls 6
  rw [qAnchor_center] at hb
  apply EdgeReach.far_endpoint_excluded (config 6) 0 (hexVertex 1 i) _ hr hb
  simpa only [dist_zero_left] using hexVertex_unit_norm i

theorem central_parameter_interior {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hc : edgePoint i t ∈ (config 6).region) : t ∈ Set.Ioo (0:ℝ) 1 := by
  constructor
  · apply lt_of_le_of_ne ht.1
    intro he
    apply vertex_not_central h i
    simpa [edgePoint, ← he] using hc
  · apply lt_of_le_of_ne ht.2
    intro he
    apply vertex_not_central h (i+1)
    simpa [edgePoint, he] using hc

set_option maxHeartbeats 1000000 in
theorem separated_edges_distance (i j : Fin 6)
    (hne : j ≠ i) (hnext : j ≠ i+1) (hprev : j ≠ i-1)
    {t u : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    1 < dist (edgePoint i t) (edgePoint j u) := by
  have hs := TriangleFrame.dist_sq_coordinates (edgePoint i t) (edgePoint j u)
  have hd := dist_nonneg (x := edgePoint i t) (y := edgePoint j u)
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  generalize he : dist (edgePoint i t) (edgePoint j u) = d at hs hd ⊢
  have ht0 := ht.1
  have ht1 := ht.2
  have hu0 := hu.1
  have hu1 := hu.2
  fin_cases i <;> fin_cases j
  all_goals try exact (hne rfl).elim
  all_goals try exact (hnext rfl).elim
  all_goals try exact (hprev rfl).elim
  all_goals
    norm_num [edgePoint, hexVertex, AffineMap.lineMap_apply, point] at hs
    ring_nf at hs
    simp only [hr] at hs
    nlinarith [sq_nonneg (t+u-1), sq_nonneg t, sq_nonneg u,
      mul_nonneg (by linarith : 0 ≤ 1-t) hu0.le,
      mul_nonneg ht0.le (by linarith : 0 ≤ 1-u)]

def touches {config : Fin 7 → UnitTriangle} (_h : StrictCover config) (i : Fin 6) : Prop :=
  ∃ t ∈ Set.Icc (0:ℝ) 1, edgePoint i t ∈ (config 6).region

theorem contacts_pairwise_adjacent {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i j : Fin 6) (hi : touches h i) (hj : touches h j) :
    j = i ∨ j = i+1 ∨ j = i-1 := by
  by_contra hno
  push_neg at hno
  obtain ⟨t, ht, hc⟩ := hi
  obtain ⟨u, hu, hd⟩ := hj
  have hgt := separated_edges_distance i j hno.1 hno.2.1 hno.2.2
    (central_parameter_interior h i ht hc) (central_parameter_interior h j hu hd)
  have hle := (config 6).dist_le_one hc hd
  linarith

/-- All actual contacts lie on at most two adjacent edges, without assuming
that positive boundary gaps exist. -/
theorem all_contacts_in_adjacent_pair {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) : ∃ k : Fin 6, ∀ i, touches h i → i=k ∨ i=k+1 := by
  classical
  by_cases he : ∃ i, touches h i
  · obtain ⟨j, hj⟩ := he
    by_cases hn : touches h (j+1)
    · refine ⟨j, ?_⟩
      intro i hi
      have h1 := contacts_pairwise_adjacent h j i hj hi
      have h2 := contacts_pairwise_adjacent h (j+1) i hn hi
      have finite : ∀ i j : Fin 6,
          (i=j ∨ i=j+1 ∨ i=j-1) →
          (i=j+1 ∨ i=(j+1)+1 ∨ i=(j+1)-1) → i=j ∨ i=j+1 := by decide
      exact finite i j h1 h2
    · refine ⟨j-1, ?_⟩
      intro i hi
      have h1 := contacts_pairwise_adjacent h j i hj hi
      have hne : i ≠ j+1 := by intro heq; subst i; exact hn hi
      rcases h1 with rfl | heq | rfl
      · exact Or.inr (by simp)
      · exact (hne heq).elim
      · exact Or.inl rfl
  · exact ⟨0, fun i hi => (he ⟨i, hi⟩).elim⟩

end
end HexagonCover.CentralBoundary
