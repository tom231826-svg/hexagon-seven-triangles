import HexagonCover.NBand.M7300_7500.Semantics
import HexagonCover.SmallestN.BoundaryBase
import HexagonCover.PointSegmentLeaf

/-! Exact identities for the original mandatory points. The numerical data
are checked here; the actual reach inequalities and central disk are supplied
by the packet-necessity theorem for the same configuration. -/
namespace HexagonCover.NBand.M7300_7500.MandatoryGeometry
open DistanceLeaf Common SmallestN.BoundaryBase

def anchorId : Fin 6 → Fin 172 := ![0,1,2,3,4,5]
def leftId : Fin 6 → Fin 172 := ![7,9,11,13,15,17]
def rightId : Fin 6 → Fin 172 := ![8,10,12,14,16,18]
def leftParameter : ℚ := 1/4
def rightParameter : Fin 6 → ℚ :=
  ![6819/10000, 6623/10000, 6261/10000, 11803/20000, 11803/20000, 73/100]
def centralRadius : ℚ := 3/32
def centralIds : List (Fin 172) := [6,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]

theorem anchors_checked : ∀ i : Fin 6, Common.point (anchorId i) = exactVertex i := by
  decide +kernel
theorem left_checked : ∀ i : Fin 6, Common.point (leftId i) =
    interpolate (exactVertex i) (exactVertex (i-1)) leftParameter := by
  decide +kernel
theorem right_checked : ∀ i : Fin 6, Common.point (rightId i) =
    interpolate (exactVertex i) (exactVertex (i+1)) (rightParameter i) := by
  decide +kernel

theorem anchor_eq (i : Fin 6) : toPlane (Common.point (anchorId i)) = SourceCoordinates.vertex i := by
  rw [anchors_checked, vertex_real]
theorem left_eq (i : Fin 6) : toPlane (Common.point (leftId i)) =
    AffineMap.lineMap (SourceCoordinates.vertex i) (SourceCoordinates.vertex (i-1))
      (leftParameter : ℝ) := by
  rw [left_checked, interpolate_real, vertex_real, vertex_real]
theorem right_eq (i : Fin 6) : toPlane (Common.point (rightId i)) =
    AffineMap.lineMap (SourceCoordinates.vertex i) (SourceCoordinates.vertex (i+1))
      (rightParameter i : ℝ) := by
  rw [right_checked, interpolate_real, vertex_real, vertex_real]

theorem central_checked : ∀ p ∈ centralIds,
    HexDomain.nonnegative (Quadratic3.sub (Quadratic3.ofRat (centralRadius ^ 2))
      (PointSegmentLeaf.normSquared (Common.point p))) = true := by
  decide +kernel

theorem central_mem (p : Fin 172) (hp : p ∈ centralIds) :
    toPlane (Common.point p) ∈ Metric.closedBall (0 : Plane) (centralRadius : ℝ) := by
  have hs := HexDomain.nonnegative_sound _ (central_checked p hp)
  simp only [Quadratic3.real_sub, Quadratic3.real_ofRat,
    Rat.cast_pow, PointSegmentLeaf.normSquared_real] at hs
  have hr : (0 : ℝ) < (centralRadius : ℝ) := by norm_num [centralRadius]
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg (toPlane (Common.point p))]

theorem mandatory_cases : ∀ owner : Fin 7, ∀ p ∈ Common.mandatory owner,
    (∃ i : Fin 6, owner = i.castSucc ∧
      (p = anchorId i ∨ p = leftId i ∨ p = rightId i)) ∨
      (owner = 6 ∧ p ∈ centralIds) := by
  decide +kernel

theorem mandatory_of_geometry (config : Fin 7 → UnitTriangle)
    (anchors : ∀ i : Fin 6, SourceCoordinates.vertex i ∈ (config i.castSucc).region)
    (left : ∀ i : Fin 6, AffineMap.lineMap (SourceCoordinates.vertex i)
      (SourceCoordinates.vertex (i-1)) (leftParameter : ℝ) ∈ (config i.castSucc).region)
    (right : ∀ i : Fin 6, AffineMap.lineMap (SourceCoordinates.vertex i)
      (SourceCoordinates.vertex (i+1)) (rightParameter i : ℝ) ∈ (config i.castSucc).region)
    (disk : Metric.closedBall (0 : Plane) (centralRadius : ℝ) ⊆ (config 6).region) :
    OwnerTree.Satisfies (Semantics.Owns config) Common.mandatory := by
  intro owner p hp
  rcases mandatory_cases owner p hp with ⟨i, rfl, ha | hl | hr⟩ | ⟨rfl, hc⟩
  · subst p
    simpa only [Semantics.Owns, anchor_eq] using anchors i
  · subst p
    simpa only [Semantics.Owns, left_eq] using left i
  · subst p
    simpa only [Semantics.Owns, right_eq] using right i
  · exact disk (central_mem p hc)

#print axioms mandatory_of_geometry
end HexagonCover.NBand.M7300_7500.MandatoryGeometry
