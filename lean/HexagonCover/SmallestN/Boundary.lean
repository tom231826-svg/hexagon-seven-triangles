import HexagonCover.SmallestN.Common
import HexagonCover.SmallestN.BoundaryBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.SmallestN.Boundary
open DistanceLeaf

def edge : Fin 170 → Fin 6 := ![0,0,0,0,0,0,0,5,0,0,1,1,2,2,3,3,4,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,5,3,0,0,0,0,0,0,0,0,0,5,3,0,0,0,0,0,0,0,0,5,3,0,0,0,0,0,0,0,5,3,0,0,0,0,0,0,5,4,4,4,4,4,0,0,0,0,0,0,4,0,0,0,0]
def parameter : Fin 170 → ℚ := ![(0),(0),(0),(0),(0),(0),(0),(83/100),(7193/10000),(83/100),(6923/10000),(83/100),(6923/10000),(83/100),(6923/10000),(83/100),(6923/10000),(83/100),(81/100),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(5/6),(2/3),(1/2),(1/3),(1/6),(1/6),(0),(0),(0),(0),(0),(0),(5/6),(1/3),(0),(0),(0),(0),(0),(0),(0),(2/3),(1/2),(0),(0),(0),(0),(0),(0),(0),(0),(1/2),(2/3),(0),(0),(0),(0),(0),(0),(0),(0),(0),(1/3),(5/6),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(1/6),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(1/6),(0),(0),(0),(0),(0),(0),(0),(0),(0),(0),(5/6),(1/3),(0),(0),(0),(0),(0),(0),(0),(0),(0),(2/3),(1/2),(0),(0),(0),(0),(0),(0),(0),(0),(1/2),(2/3),(0),(0),(0),(0),(0),(0),(0),(1/3),(5/6),(0),(0),(0),(0),(0),(0),(1/6),(1/6),(1/3),(1/2),(2/3),(5/6),(0),(0),(0),(0),(0),(0),(41/50),(0),(0),(0),(0)]

theorem restricted_checked : ∀ p : Fin 170, Common.allowed p 6 = false →
    BoundaryBase.check (Common.point p) (edge p) (parameter p) = true := by
  decide +kernel

theorem restricted_on_edge (p : Fin 170) (hp : Common.allowed p 6 = false) :
    (parameter p : ℝ) ∈ Set.Icc 0 1 ∧ toPlane (Common.point p) =
      AffineMap.lineMap (SourceCoordinates.vertex (edge p))
        (SourceCoordinates.vertex (edge p+1)) (parameter p : ℝ) :=
  BoundaryBase.check_sound _ _ _ (restricted_checked p hp)

#print axioms restricted_on_edge
end HexagonCover.SmallestN.Boundary
