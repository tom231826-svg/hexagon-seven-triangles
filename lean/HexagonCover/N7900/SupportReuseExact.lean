import HexagonCover.SmallestN.SupportCertificates0000
import HexagonCover.SmallestN.SupportCertificates0002
import HexagonCover.SmallestN.SupportCertificates0003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SupportReuseExact
open DistanceLeaf SupportWitness

namespace C000015
def sourcePoints : Fin 4 → ExactPoint := ![fromXYZ (-1/12) (0) (-1/12),fromXYZ (-1/12) (0) (1/12),fromXYZ (5/6) (0) (0),fromXYZ (7/12) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 4,
    HexagonCover.SmallestN.SupportCertificates0000.C000017.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 4, HexagonCover.SmallestN.SupportCertificates0000.C000017.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0000.C000017.certificate
end C000015

namespace C000017
def sourcePoints : Fin 4 → ExactPoint := ![fromXYZ (-1/12) (0) (-1/12),fromXYZ (-1/12) (0) (1/12),fromXYZ (2/3) (0) (-1/6),fromXYZ (7/12) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 4,
    HexagonCover.SmallestN.SupportCertificates0000.C000019.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 4, HexagonCover.SmallestN.SupportCertificates0000.C000019.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0000.C000019.certificate
end C000017

namespace C000086
def sourcePoints : Fin 6 → ExactPoint := ![fromXYZ (-1/12) (0) (-1/12),fromXYZ (-1/6) (0) (0),fromXYZ (1/200) (0) (48/173),fromXYZ (1/3) (0) (1/3),fromXYZ (1/6) (0) (1/3),fromXYZ (3/4) (0) (-1/12)]
theorem exact_identity : ∀ i : Fin 6,
    HexagonCover.SmallestN.SupportCertificates0002.C000075.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 6, HexagonCover.SmallestN.SupportCertificates0002.C000075.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0002.C000075.certificate
end C000086

namespace C000101
def sourcePoints : Fin 4 → ExactPoint := ![fromXYZ (-1/12) (0) (-1/12),fromXYZ (-1/3) (0) (0),fromXYZ (1/2) (0) (1/6),fromXYZ (7/12) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 4,
    HexagonCover.SmallestN.SupportCertificates0003.C000126.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 4, HexagonCover.SmallestN.SupportCertificates0003.C000126.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0003.C000126.certificate
end C000101

namespace C000145
def sourcePoints : Fin 4 → ExactPoint := ![fromXYZ (-1/12) (0) (-1/12),fromXYZ (-1/6) (0) (0),fromXYZ (0) (0) (1/3),fromXYZ (3/4) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 4,
    HexagonCover.SmallestN.SupportCertificates0003.C000096.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 4, HexagonCover.SmallestN.SupportCertificates0003.C000096.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0003.C000096.certificate
end C000145

namespace C000146
def sourcePoints : Fin 5 → ExactPoint := ![fromXYZ (-1/12) (0) (-1/12),fromXYZ (-1/6) (0) (0),fromXYZ (0) (0) (1/3),fromXYZ (7/12) (0) (-1/12),fromXYZ (7/12) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 5,
    HexagonCover.SmallestN.SupportCertificates0003.C000097.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 5, HexagonCover.SmallestN.SupportCertificates0003.C000097.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0003.C000097.certificate
end C000146

namespace C000148
def sourcePoints : Fin 4 → ExactPoint := ![fromXYZ (-1/6) (0) (0),fromXYZ (0) (0) (-1/6),fromXYZ (0) (0) (1/3),fromXYZ (7/12) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 4,
    HexagonCover.SmallestN.SupportCertificates0003.C000099.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 4, HexagonCover.SmallestN.SupportCertificates0003.C000099.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0003.C000099.certificate
end C000148

namespace C000155
def sourcePoints : Fin 5 → ExactPoint := ![fromXYZ (-1/12) (0) (-1/12),fromXYZ (-1/12) (0) (5/12),fromXYZ (-1/6) (0) (0),fromXYZ (1/2) (0) (0),fromXYZ (7/12) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 5,
    HexagonCover.SmallestN.SupportCertificates0003.C000111.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 5, HexagonCover.SmallestN.SupportCertificates0003.C000111.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0003.C000111.certificate
end C000155

namespace C000157
def sourcePoints : Fin 4 → ExactPoint := ![fromXYZ (-1/4) (0) (1/4),fromXYZ (-1/6) (0) (0),fromXYZ (1/12) (0) (-1/4),fromXYZ (7/12) (0) (1/12)]
theorem exact_identity : ∀ i : Fin 4,
    HexagonCover.SmallestN.SupportCertificates0003.C000114.certificate.certificate.points i = sourcePoints i := by
  change ∀ i : Fin 4, HexagonCover.SmallestN.SupportCertificates0003.C000114.points i = sourcePoints i
  decide +kernel
def certificate : CheckedCertificate := HexagonCover.SmallestN.SupportCertificates0003.C000114.certificate
end C000157

#print axioms C000015.exact_identity
#print axioms C000017.exact_identity
#print axioms C000086.exact_identity
#print axioms C000101.exact_identity
#print axioms C000145.exact_identity
#print axioms C000146.exact_identity
#print axioms C000148.exact_identity
#print axioms C000155.exact_identity
#print axioms C000157.exact_identity

end HexagonCover.N7900.SupportReuseExact
