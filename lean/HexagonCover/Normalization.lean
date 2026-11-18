import HexagonCover.Anchors

/-! Preserve the actual seven pieces while moving to H1 and the original
certificate role order: six outer vertices first, then the center. The earlier
anchor theorem uses center first, so this reindexing is explicit. -/
namespace HexagonCover.Normalization
noncomputable section

def qAnchor (s : ℝ) : Fin 7 → Plane :=
  ![hexVertex s 0, hexVertex s 1, hexVertex s 2, hexVertex s 3,
    hexVertex s 4, hexVertex s 5, 0]

theorem qAnchor_eq_outer (s : ℝ) (i : Fin 7) :
    qAnchor s i = outerAnchor s (finRotate 7 i) := by
  fin_cases i <;> norm_num [qAnchor, finRotate_apply, outerAnchor] <;> rfl

theorem unit_hexagon_subset {s : ℝ} (hs : 1 < s) : Hexagon 1 ⊆ Hexagon s := by
  apply convexHull_min
  · rintro _ ⟨i, rfl⟩
    exact interior_subset (unitVertex_mem_interior_of_center hs
      (zero_mem_interior_hexagon (by linarith)) i)
  · exact convex_hexagon s

theorem covers_one_of_expanded_cover {s : ℝ} (hs : 1 < s)
    (config : Fin 7 → UnitTriangle) (covered : Covers s config) : Covers 1 config :=
  (unit_hexagon_subset hs).trans covered

theorem covers_reindex {s : ℝ} (config : Fin 7 → UnitTriangle)
    (covered : Covers s config) (σ : Equiv.Perm (Fin 7)) :
    Covers s (fun i => config (σ i)) := by
  intro p hp
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (covered hp)
  obtain ⟨i, rfl⟩ := σ.surjective j
  exact Set.mem_iUnion.mpr ⟨i, hj⟩

/-- The original actual pieces, only permuted into certificate roles, cover H1
and contain positive balls about their exact required anchors. -/
theorem q_roles_of_expanded_cover {s : ℝ} (hs : 1 < s)
    (config : Fin 7 → UnitTriangle) (covered : Covers s config) :
    ∃ σ : Equiv.Perm (Fin 7),
      Covers 1 (fun i => config (σ i)) ∧
      (∀ i, qAnchor s i ∈ (config (σ i)).region) ∧
      (∀ i, ∃ r > 0, Metric.ball (qAnchor 1 i) r ⊆ (config (σ i)).region) := by
  obtain ⟨σ, hanchors, hballs⟩ := anchor_disks_of_cover hs config covered
  let τ := (finRotate 7).trans σ
  refine ⟨τ, covers_reindex config (covers_one_of_expanded_cover hs config covered) τ, ?_, ?_⟩
  · intro i
    rw [qAnchor_eq_outer]
    exact hanchors (finRotate 7 i)
  · intro i
    rw [qAnchor_eq_outer]
    exact hballs (finRotate 7 i)

end
end HexagonCover.Normalization
