import HexagonCover.NBand.M7100_7300.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.Arithmetic.Run0000
open Common Semantics DistanceLeaf

theorem checked_0003 : CheckedFact 3 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 3) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0004 : CheckedFact 4 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 4) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0005 : CheckedFact 5 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 5) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0008 : CheckedFact 8 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 8) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0009 : CheckedFact 9 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 9) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0010 : CheckedFact 10 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 10) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0013 : CheckedFact 13 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 13) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0014 : CheckedFact 14 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 14) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0015 : CheckedFact 15 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 15) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0018 : CheckedFact 18 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 18) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0019 : CheckedFact 19 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 19) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0020 : CheckedFact 20 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 20) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0021 : CheckedFact 21 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 21) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0022 : CheckedFact 22 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 22) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0023 : CheckedFact 23 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 23)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0024 : CheckedFact 24 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 24) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0025 : CheckedFact 25 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 25) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0026 : CheckedFact 26 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 26) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0027 : CheckedFact 27 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 27) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0028 : CheckedFact 28 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 28) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0030 : CheckedFact 30 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 30) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0031 : CheckedFact 31 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 31) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0032 : CheckedFact 32 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 32) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0033 : CheckedFact 33 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 33) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0034 : CheckedFact 34 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 34) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0035 : CheckedFact 35 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 35) (positions := (22,23))
      (by decide +kernel) T contained

theorem checked_0036 : CheckedFact 36 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 36) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0037 : CheckedFact 37 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 37) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0039 : CheckedFact 39 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 39) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0040 : CheckedFact 40 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 40) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0041 : CheckedFact 41 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 41) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0042 : CheckedFact 42 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 42) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0043 : CheckedFact 43 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 43) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0047 : CheckedFact 47 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 47) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0048 : CheckedFact 48 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 48) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0049 : CheckedFact 49 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 49) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0050 : CheckedFact 50 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 50) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0051 : CheckedFact 51 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 51) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0052 : CheckedFact 52 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 52) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0054 : CheckedFact 54 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 54) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0055 : CheckedFact 55 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 55) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0057 : CheckedFact 57 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 57) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0058 : CheckedFact 58 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 58) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0059 : CheckedFact 59 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 59) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0060 : CheckedFact 60 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 60) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0062 : CheckedFact 62 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 62) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0063 : CheckedFact 63 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 63) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0064 : CheckedFact 64 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 64) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0065 : CheckedFact 65 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 65) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0066 : CheckedFact 66 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 66) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0068 : CheckedFact 68 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 68) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0069 : CheckedFact 69 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 69) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0070 : CheckedFact 70 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 70) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0071 : CheckedFact 71 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 71) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0072 : CheckedFact 72 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 72) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0073 : CheckedFact 73 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 73) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0074 : CheckedFact 74 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 74) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0075 : CheckedFact 75 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 75) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0076 : CheckedFact 76 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 76) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0077 : CheckedFact 77 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 77) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0078 : CheckedFact 78 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 78) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0079 : CheckedFact 79 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 79) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0080 : CheckedFact 80 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 80) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0081 : CheckedFact 81 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 81) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0082 : CheckedFact 82 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 82) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0083 : CheckedFact 83 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 83) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0084 : CheckedFact 84 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 84) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0085 : CheckedFact 85 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 85) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0086 : CheckedFact 86 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 86) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0087 : CheckedFact 87 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 87) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0088 : CheckedFact 88 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 88) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0089 : CheckedFact 89 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 89) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0090 : CheckedFact 90 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 90) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0091 : CheckedFact 91 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 91) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0094 : CheckedFact 94 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 94) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0095 : CheckedFact 95 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 95) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0096 : CheckedFact 96 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 96) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0097 : CheckedFact 97 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 97) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0098 : CheckedFact 98 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 98) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0099 : CheckedFact 99 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 99) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0100 : CheckedFact 100 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 100) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0101 : CheckedFact 101 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 101) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0104 : CheckedFact 104 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 104) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0105 : CheckedFact 105 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 105) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0106 : CheckedFact 106 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 106) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0107 : CheckedFact 107 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 107) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0108 : CheckedFact 108 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 108) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0110 : CheckedFact 110 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 110) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0111 : CheckedFact 111 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 111) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0112 : CheckedFact 112 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 112) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0114 : CheckedFact 114 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 114) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0116 : CheckedFact 116 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 116) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0117 : CheckedFact 117 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 117) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0118 : CheckedFact 118 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 118) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0120 : CheckedFact 120 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 120) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0121 : CheckedFact 121 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 121) (positions := (22,25))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7100_7300.Arithmetic.Run0000
