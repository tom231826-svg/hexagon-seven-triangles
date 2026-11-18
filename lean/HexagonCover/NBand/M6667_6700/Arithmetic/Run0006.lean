import HexagonCover.NBand.M6667_6700.Semantics
import HexagonCover.NISubsetData.Batch0002
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.Arithmetic.Run0006
open Common Semantics DistanceLeaf

theorem checked_0993 : CheckedFact 993 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 993) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0999 : CheckedFact 999 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 999) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1000 : CheckedFact 1000 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1000) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1001 : CheckedFact 1001 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1001) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1003 : CheckedFact 1003 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1003) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1004 : CheckedFact 1004 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1004) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1005 : CheckedFact 1005 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1005) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1007 : CheckedFact 1007 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1007) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_1008 : CheckedFact 1008 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1008) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1009 : CheckedFact 1009 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1009) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1011 : CheckedFact 1011 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1011) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1012 : CheckedFact 1012 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1012) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1013 : CheckedFact 1013 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1013) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1015 : CheckedFact 1015 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1015) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1025 : CheckedFact 1025 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1025) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1028 : CheckedFact 1028 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1028) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1029 : CheckedFact 1029 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1029) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_1032 : CheckedFact 1032 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1032)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1034 : CheckedFact 1034 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1034) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1042 : CheckedFact 1042 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1042) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1043 : CheckedFact 1043 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1043) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1044 : CheckedFact 1044 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1044) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1046 : CheckedFact 1046 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0002.c0005_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_1049 : CheckedFact 1049 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1049) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1050 : CheckedFact 1050 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1050) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1051 : CheckedFact 1051 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1051) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1053 : CheckedFact 1053 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1053) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1054 : CheckedFact 1054 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1054) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1055 : CheckedFact 1055 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1055) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1057 : CheckedFact 1057 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1057) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1058 : CheckedFact 1058 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1058) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1059 : CheckedFact 1059 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1059) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1060 : CheckedFact 1060 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1060) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1062 : CheckedFact 1062 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1062) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1063 : CheckedFact 1063 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1063) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1064 : CheckedFact 1064 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1064) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1068 : CheckedFact 1068 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1068) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1070 : CheckedFact 1070 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1070) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1072 : CheckedFact 1072 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1072) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1073 : CheckedFact 1073 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1073)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1076 : CheckedFact 1076 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1076) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1077 : CheckedFact 1077 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1077) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1078 : CheckedFact 1078 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1078) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1079 : CheckedFact 1079 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1079) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1080 : CheckedFact 1080 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1080) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1084 : CheckedFact 1084 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1084) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1085 : CheckedFact 1085 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1085) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1086 : CheckedFact 1086 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1086) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1087 : CheckedFact 1087 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1087) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1088 : CheckedFact 1088 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1088) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_1091 : CheckedFact 1091 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1091) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1092 : CheckedFact 1092 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1092) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1097 : CheckedFact 1097 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1097) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1098 : CheckedFact 1098 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1098) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1101 : CheckedFact 1101 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1101) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1103 : CheckedFact 1103 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1103) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1104 : CheckedFact 1104 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1104) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1105 : CheckedFact 1105 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1105) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1106 : CheckedFact 1106 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1106) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1107 : CheckedFact 1107 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1107) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1108 : CheckedFact 1108 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1108) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1109 : CheckedFact 1109 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1109) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1112 : CheckedFact 1112 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1112) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1119 : CheckedFact 1119 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1119) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1120 : CheckedFact 1120 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1120) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1121 : CheckedFact 1121 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1121) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1122 : CheckedFact 1122 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1122) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1123 : CheckedFact 1123 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1123) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1124 : CheckedFact 1124 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1124) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1125 : CheckedFact 1125 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1125) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1128 : CheckedFact 1128 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1128) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1129 : CheckedFact 1129 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1129) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1131 : CheckedFact 1131 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1131) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_1132 : CheckedFact 1132 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1132) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1135 : CheckedFact 1135 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1135) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1137 : CheckedFact 1137 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1137) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1138 : CheckedFact 1138 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1138) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1144 : CheckedFact 1144 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1144) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1145 : CheckedFact 1145 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1145) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_1146 : CheckedFact 1146 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1146) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1153 : CheckedFact 1153 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1153) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1155 : CheckedFact 1155 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1155) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1156 : CheckedFact 1156 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1156) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1157 : CheckedFact 1157 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1157) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1158 : CheckedFact 1158 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1158) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1163 : CheckedFact 1163 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1163) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1164 : CheckedFact 1164 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1164) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1165 : CheckedFact 1165 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1165) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1166 : CheckedFact 1166 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1166) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1170 : CheckedFact 1170 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1170) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1171 : CheckedFact 1171 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1171) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1172 : CheckedFact 1172 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1172) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1173 : CheckedFact 1173 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1173) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_1174 : CheckedFact 1174 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1174) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1175 : CheckedFact 1175 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1175) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1176 : CheckedFact 1176 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1176) (positions := (0,3))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6667_6700.Arithmetic.Run0006
