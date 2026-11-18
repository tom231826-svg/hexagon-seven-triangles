import HexagonCover.SupportWitness
import HexagonCover.DistanceData.Common

namespace HexagonCover.SupportWitnessData
open DistanceLeaf

structure BoundWitness where
  family : DistanceData.Family
  factId : Nat
  role : Fin 7
  anchorId : Nat
  pointIds : List Nat
  points : List ExactPoint
  originalFlag : Bool
  journalLine : Nat
  identity : String
  subsetId : Nat

structure CheckedWitness where
  data : BoundWitness
  proof : SupportWitness.CheckedCertificate
  member : SupportWitness.membershipCheck data.points proof.certificate = true

theorem CheckedWitness.excluded (w : CheckedWitness) (T : UnitTriangle)
    (contained : ∀ p ∈ w.data.points, toPlane p ∈ T.region) : False :=
  w.proof.excluded w.data.points w.member T contained

end HexagonCover.SupportWitnessData
