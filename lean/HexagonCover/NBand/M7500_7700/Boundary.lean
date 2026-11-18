import HexagonCover.NBand.M7500_7700.Common
import HexagonCover.SmallestN.BoundaryBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.Boundary
open DistanceLeaf SmallestN

def edge : Fin 173 → Fin 6 := ![0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 0, 0, 0, 0, 5, 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0]
def parameter : Fin 173 → ℚ := ![(0), (0), (0), (0), (0), (0), (0), (77/100), (6899/10000), (77/100), (3337/5000), (77/100), (3133/5000), (77/100), (12293/20000), (77/100), (12293/20000), (77/100), (3/4), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (5/6), (2/3), (1/2), (1/3), (1/6), (1/6), (0), (0), (0), (0), (0), (0), (5/6), (1/3), (0), (0), (0), (0), (0), (0), (0), (2/3), (1/2), (0), (0), (0), (0), (0), (0), (0), (0), (1/2), (2/3), (0), (0), (0), (0), (0), (0), (0), (0), (0), (1/3), (5/6), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (1/6), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (1/6), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (5/6), (1/3), (0), (0), (0), (0), (0), (0), (0), (0), (0), (2/3), (1/2), (0), (0), (0), (0), (0), (0), (0), (0), (1/2), (2/3), (0), (0), (0), (0), (0), (0), (0), (1/3), (5/6), (0), (0), (0), (0), (0), (0), (1/6), (1/6), (1/3), (1/2), (2/3), (5/6), (0), (0), (0), (0), (0), (0), (19/25), (0), (0), (0), (0), (0), (0), (0)]

theorem restricted_checked : ∀ p : Fin 173, Common.allowed p 6 = false →
    BoundaryBase.check (Common.point p) (edge p) (parameter p) = true := by
  decide +kernel

theorem restricted_on_edge (p : Fin 173) (hp : Common.allowed p 6 = false) :
    (parameter p : ℝ) ∈ Set.Icc 0 1 ∧ toPlane (Common.point p) =
      AffineMap.lineMap (SourceCoordinates.vertex (edge p))
        (SourceCoordinates.vertex (edge p+1)) (parameter p : ℝ) :=
  BoundaryBase.check_sound _ _ _ (restricted_checked p hp)

#print axioms restricted_on_edge
end HexagonCover.NBand.M7500_7700.Boundary
