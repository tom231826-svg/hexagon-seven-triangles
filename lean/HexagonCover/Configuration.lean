import HexagonCover.Normalization
import HexagonCover.EdgeReach
import HexagonCover.StandardCover

/-! Intermediate geometric state attached to one actual seven-piece
configuration. This is not an extra hypothesis in the target CoverConjecture:
every hypothetical expanded cover is proved to produce this state. -/
namespace HexagonCover.Configuration
open Normalization
noncomputable section

structure StrictCover (config : Fin 7 → UnitTriangle) : Prop where
  covered : Covers 1 config
  anchorBalls : ∀ i, ∃ r > 0, Metric.ball (qAnchor 1 i) r ⊆ (config i).region

theorem from_expanded_cover {s : ℝ} (hs : 1 < s) (config : Fin 7 → UnitTriangle)
    (covered : Covers s config) :
    ∃ σ : Equiv.Perm (Fin 7), StrictCover (fun i => config (σ i)) := by
  obtain ⟨σ, hcover, _, hballs⟩ := q_roles_of_expanded_cover hs config covered
  exact ⟨σ, hcover, hballs⟩

theorem qAnchor_outer (i : Fin 6) : qAnchor 1 i.castSucc = hexVertex 1 i := by
  fin_cases i <;> rfl

theorem qAnchor_center : qAnchor 1 (6 : Fin 7) = 0 := rfl

theorem anchor_mem {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 7) :
    qAnchor 1 i ∈ (config i).region := by
  obtain ⟨r, hr, hball⟩ := h.anchorBalls i
  exact hball (Metric.mem_ball_self hr)

theorem dist_from_strict_anchor_lt_one (T : UnitTriangle) (u : Plane)
    {r : ℝ} (hr : 0 < r) (ball : Metric.ball u r ⊆ T.region)
    (p : Plane) (hp : p ∈ T.region) : dist u p < 1 := by
  have hu : u ∈ T.region := ball (Metric.mem_ball_self hr)
  have hd := T.dist_le_one hu hp
  apply lt_of_le_of_ne hd
  intro heq
  exact EdgeReach.far_endpoint_excluded T u p heq hr ball hp

theorem adjacent_distance (i : Fin 6) :
    dist (hexVertex 1 i) (hexVertex 1 (i+1)) = 1 := by
  have h := StandardCover.fan_edge i (1 : Fin 3) 2 (by decide)
  exact h

theorem previous_distance (i : Fin 6) :
    dist (hexVertex 1 i) (hexVertex 1 (i-1)) = 1 := by
  have h := adjacent_distance (i-1)
  simpa only [sub_add_cancel, dist_comm] using h

def rightReach {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    EdgeReach.Reach (config i.castSucc) (hexVertex 1 i) (hexVertex 1 (i+1)) := by
  apply Classical.choice
  obtain ⟨r, hr, hball⟩ := h.anchorBalls i.castSucc
  rw [qAnchor_outer] at hball
  exact EdgeReach.exists_reach _ _ _ (adjacent_distance i) hr hball

def leftReach {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    EdgeReach.Reach (config i.castSucc) (hexVertex 1 i) (hexVertex 1 (i-1)) := by
  apply Classical.choice
  obtain ⟨r, hr, hball⟩ := h.anchorBalls i.castSucc
  rw [qAnchor_outer] at hball
  exact EdgeReach.exists_reach _ _ _ (previous_distance i) hr hball

def a {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) : ℝ :=
  (leftReach h i).length
def b {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) : ℝ :=
  (rightReach h i).length

theorem reach_bounds {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    0 < a h i ∧ a h i < 1 ∧ 0 < b h i ∧ b h i < 1 :=
  ⟨(leftReach h i).positive, (leftReach h i).lt_one,
    (rightReach h i).positive, (rightReach h i).lt_one⟩

/-- Conditional assembly interface only: its exclusion premise remains an
outstanding theorem, not an axiom or a proof of the target. -/
theorem target_of_strict_cover_exclusion
    (exclusion : ∀ config : Fin 7 → UnitTriangle, ¬ StrictCover config) : CoverConjecture := by
  intro s hs config covered
  obtain ⟨σ, h⟩ := from_expanded_cover hs config covered
  exact exclusion (fun i => config (σ i)) h

end
end HexagonCover.Configuration
