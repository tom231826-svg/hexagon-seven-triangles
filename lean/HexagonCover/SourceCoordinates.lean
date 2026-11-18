import HexagonCover.ReachEquiv
import HexagonCover.HeavyTransport
import HexagonCover.CentralDisk

/-! The N/source continuous geometry uses role0=(1/2,h),...,role5=(1,0),
whereas Q and StrictCover use role0=(1,0). This adapter physically rotates ALL
seven actual pieces by +60 degrees and preserves role labels. Raw N certificate
coordinates must not be silently identified with the Q anchor convention. -/
namespace HexagonCover.SourceCoordinates
open HexagonCover.Configuration Symmetry
noncomputable section

def vertex (i : Fin 6) : Plane := hexVertex 1 (i+1)
def rotateConfig (config : Fin 7 → UnitTriangle) : Fin 7 → UnitTriangle :=
  fun i => mapTriangle turn (config i)

theorem vertex_table : vertex =
    ![point (1/2) NICertificate.halfRoot, point (-1/2) NICertificate.halfRoot,
      point (-1) 0, point (-1/2) (-NICertificate.halfRoot),
      point (1/2) (-NICertificate.halfRoot), point 1 0] := by
  funext i
  fin_cases i <;> norm_num [vertex,hexVertex,NICertificate.halfRoot]
  all_goals simp only [neg_div]

theorem turn_vertex_eq (i : Fin 6) : turn (hexVertex 1 i)=vertex i := turn_vertex 1 i

theorem covered {config : Fin 7 → UnitTriangle} (h : StrictCover config) :
    Covers 1 (rotateConfig config) := map_cover turn (turn_hexagon 1) config h.covered

theorem anchors {config : Fin 7 → UnitTriangle} (h : StrictCover config) (i : Fin 6) :
    vertex i ∈ (rotateConfig config i.castSucc).region := by
  rw [rotateConfig,map_region,←turn_vertex_eq]
  exact ⟨hexVertex 1 i,by simpa only [qAnchor_outer] using anchor_mem h i.castSucc,rfl⟩

theorem right_endpoint {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hle : t ≤ b h i) :
    AffineMap.lineMap (vertex i) (vertex (i+1)) t ∈
      (rotateConfig config i.castSucc).region := by
  rw [rotateConfig,map_region,←turn_vertex_eq,←turn_vertex_eq,
    ←ReachEquiv.lineMap_apply]
  exact ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i+1)) t,
    ((rightReach h i).character t ht).mpr hle,rfl⟩

theorem left_endpoint {config : Fin 7 → UnitTriangle} (h : StrictCover config)
    (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hle : t ≤ a h i) :
    AffineMap.lineMap (vertex i) (vertex (i-1)) t ∈
      (rotateConfig config i.castSucc).region := by
  rw [rotateConfig,map_region,←turn_vertex_eq,←turn_vertex_eq,
    ←ReachEquiv.lineMap_apply]
  exact ⟨AffineMap.lineMap (hexVertex 1 i) (hexVertex 1 (i-1)) t,
    ((leftReach h i).character t ht).mpr hle,rfl⟩

theorem central_disk {config : Fin 7 → UnitTriangle} {r : ℝ}
    (disk : Metric.closedBall (0:Plane) r ⊆ (config 6).region) :
    Metric.closedBall (0:Plane) r ⊆ (rotateConfig config 6).region := by
  intro p hp
  rw [rotateConfig,map_region]
  refine ⟨turn.symm p,disk ?_,turn.apply_symm_apply p⟩
  have he : ‖turn.symm p‖=‖p‖ := by
    have hh := turn_norm (turn.symm p)
    rw [turn.apply_symm_apply] at hh
    exact hh.symm
  simpa only [Metric.mem_closedBall,dist_zero_right,he] using hp

theorem separation {config : Fin 7 → UnitTriangle} (i : Fin 7) {r : ℝ}
    (sep : ∀p∈(config i).region,r ≤ ‖p‖) :
    ∀p∈(rotateConfig config i).region,r ≤ ‖p‖ := turn_nonintruding sep

end
end HexagonCover.SourceCoordinates
