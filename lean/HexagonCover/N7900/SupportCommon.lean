import HexagonCover.N7900.Common
import HexagonCover.SupportWitness

namespace HexagonCover.N7900
open DistanceLeaf

structure SupportEntry where
  id : Fin 763
  proof : SupportWitness.CheckedCertificate
  member : SupportWitness.membershipCheck (Common.obligations id) proof.certificate = true

theorem SupportEntry.excluded (row : SupportEntry) (T : UnitTriangle)
    (contained : ∀ p ∈ Common.obligations row.id, toPlane p ∈ T.region) : False :=
  row.proof.excluded (Common.obligations row.id) row.member T contained

end HexagonCover.N7900
