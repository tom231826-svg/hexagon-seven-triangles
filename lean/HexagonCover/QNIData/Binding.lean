import HexagonCover.GenericNI
import HexagonCover.DistanceData.Common

/-! Original Q source-use identities attached to actual checked NI exclusions.
Metadata identities do not assert closure of the original ownership trees. -/
namespace HexagonCover.QNIData
open DistanceLeaf

structure BoundInput where
  family : DistanceData.Family
  factId : Nat
  role : Fin 7
  anchorId : Nat
  pointIds : List Nat
  points : List ExactPoint
  radiusSquared : ℚ
  originalFlag : Bool
  originalToken : Nat
  identity : String
  bindingSHA256 : String
  certificateSHA256 : String

structure CheckedInput where
  data : BoundInput
  excluded : ∀ T : UnitTriangle,
    (∀ p ∈ data.points, toPlane p ∈ T.region) →
    (∀ p ∈ T.region, (data.radiusSquared:ℝ) ≤ ‖p‖^2) → False

end HexagonCover.QNIData
