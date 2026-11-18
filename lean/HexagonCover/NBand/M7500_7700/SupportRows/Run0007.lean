import HexagonCover.NBand.M7500_7700.Semantics
import HexagonCover.NBand.Support.Run0043
import HexagonCover.NBand.Support.Run0050
import HexagonCover.NBand.Support.Run0051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SupportRows.Run0007
open Common Semantics SupportWitness

theorem checked_0984 : CheckedFact 984 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0043.C002080.certificate.excluded (Common.obligations 984) (by decide +kernel) T contained

theorem checked_0985 : CheckedFact 985 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002496.certificate.excluded (Common.obligations 985) (by decide +kernel) T contained

theorem checked_0989 : CheckedFact 989 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002497.certificate.excluded (Common.obligations 989) (by decide +kernel) T contained

theorem checked_0991 : CheckedFact 991 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002498.certificate.excluded (Common.obligations 991) (by decide +kernel) T contained

theorem checked_0992 : CheckedFact 992 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002499.certificate.excluded (Common.obligations 992) (by decide +kernel) T contained

theorem checked_0993 : CheckedFact 993 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002500.certificate.excluded (Common.obligations 993) (by decide +kernel) T contained

theorem checked_0994 : CheckedFact 994 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0050.C002417.certificate.excluded (Common.obligations 994) (by decide +kernel) T contained

theorem checked_0995 : CheckedFact 995 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0050.C002418.certificate.excluded (Common.obligations 995) (by decide +kernel) T contained

theorem checked_0996 : CheckedFact 996 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002496.certificate.excluded (Common.obligations 996) (by decide +kernel) T contained

theorem checked_0997 : CheckedFact 997 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002501.certificate.excluded (Common.obligations 997) (by decide +kernel) T contained

theorem checked_0998 : CheckedFact 998 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002502.certificate.excluded (Common.obligations 998) (by decide +kernel) T contained

theorem checked_0999 : CheckedFact 999 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002503.certificate.excluded (Common.obligations 999) (by decide +kernel) T contained

theorem checked_1001 : CheckedFact 1001 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0043.C002111.certificate.excluded (Common.obligations 1001) (by decide +kernel) T contained

theorem checked_1002 : CheckedFact 1002 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002504.certificate.excluded (Common.obligations 1002) (by decide +kernel) T contained

theorem checked_1003 : CheckedFact 1003 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002505.certificate.excluded (Common.obligations 1003) (by decide +kernel) T contained

theorem checked_1004 : CheckedFact 1004 where
  excluded T contained _ :=
    HexagonCover.NBand.Support.Run0051.C002506.certificate.excluded (Common.obligations 1004) (by decide +kernel) T contained

end HexagonCover.NBand.M7500_7700.SupportRows.Run0007
