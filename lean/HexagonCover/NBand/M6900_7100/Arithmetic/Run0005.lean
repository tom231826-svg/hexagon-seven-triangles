import HexagonCover.NBand.M6900_7100.Semantics
import HexagonCover.NISubsetData.Batch0004
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.Arithmetic.Run0005
open Common Semantics DistanceLeaf

theorem checked_0947 : CheckedFact 947 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 947) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0950 : CheckedFact 950 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 950) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0952 : CheckedFact 952 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 952) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0954 : CheckedFact 954 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 954) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0955 : CheckedFact 955 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 955) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0956 : CheckedFact 956 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 956) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0966 : CheckedFact 966 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 966) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0985 : CheckedFact 985 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 985) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0988 : CheckedFact 988 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 988) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0989 : CheckedFact 989 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 989) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0991 : CheckedFact 991 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0004.c0007_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_1004 : CheckedFact 1004 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1004) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1009 : CheckedFact 1009 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1009) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1015 : CheckedFact 1015 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1015) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1016 : CheckedFact 1016 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1016) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1021 : CheckedFact 1021 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1021) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1022 : CheckedFact 1022 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1022) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1025 : CheckedFact 1025 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1025) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1026 : CheckedFact 1026 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1026) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1027 : CheckedFact 1027 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1027) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1028 : CheckedFact 1028 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1028) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1031 : CheckedFact 1031 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1031) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1034 : CheckedFact 1034 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1034) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1035 : CheckedFact 1035 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1035) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1036 : CheckedFact 1036 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1036) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1037 : CheckedFact 1037 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1037) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1038 : CheckedFact 1038 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1038) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1044 : CheckedFact 1044 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1044) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1050 : CheckedFact 1050 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1050) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1051 : CheckedFact 1051 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1051) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1052 : CheckedFact 1052 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1052) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1053 : CheckedFact 1053 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1053) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1055 : CheckedFact 1055 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1055) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1056 : CheckedFact 1056 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1056) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1075 : CheckedFact 1075 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1075) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1099 : CheckedFact 1099 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1099) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1106 : CheckedFact 1106 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1106) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1118 : CheckedFact 1118 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1118) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1127 : CheckedFact 1127 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1127) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1131 : CheckedFact 1131 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1131) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1132 : CheckedFact 1132 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1132) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1133 : CheckedFact 1133 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1133) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1134 : CheckedFact 1134 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1134) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1135 : CheckedFact 1135 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1135) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1154 : CheckedFact 1154 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1154) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1159 : CheckedFact 1159 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1159) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1160 : CheckedFact 1160 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1160) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1167 : CheckedFact 1167 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1167) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1168 : CheckedFact 1168 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1168) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1170 : CheckedFact 1170 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1170) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1171 : CheckedFact 1171 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1171) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1174 : CheckedFact 1174 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1174) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1177 : CheckedFact 1177 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1177) (positions := (0,4))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6900_7100.Arithmetic.Run0005
