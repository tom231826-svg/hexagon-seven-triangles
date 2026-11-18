import HexagonCover.N7900.Semantics
import HexagonCover.PointSegmentLeaf
import HexagonCover.NISubsetData.Batch0006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.Arithmetic
open Common Semantics DistanceLeaf

theorem checked_0001 : CheckedFact 1 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0002 : CheckedFact 2 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 2) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0003 : CheckedFact 3 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 3) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0006 : CheckedFact 6 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 6) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0007 : CheckedFact 7 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 7) (positions := (1,3))
      (by decide +kernel) T contained

theorem checked_0008 : CheckedFact 8 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 8) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0009 : CheckedFact 9 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 9) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0010 : CheckedFact 10 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 10) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0012 : CheckedFact 12 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 12) (positions := (2,3))
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

theorem checked_0016 : CheckedFact 16 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 16) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0017 : CheckedFact 17 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 17)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0018 : CheckedFact 18 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 18) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 21) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0022 : CheckedFact 22 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 22) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0023 : CheckedFact 23 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 23) (positions := (21,22))
      (by decide +kernel) T contained

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
    DistanceLeaf.checkWitness_sound (points := obligations 27) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0028 : CheckedFact 28 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 28) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0029 : CheckedFact 29 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 29) (positions := (21,22))
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
    DistanceLeaf.checkWitness_sound (points := obligations 32) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0033 : CheckedFact 33 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 33) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0034 : CheckedFact 34 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 34) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0035 : CheckedFact 35 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 35) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0036 : CheckedFact 36 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 36) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0037 : CheckedFact 37 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 37) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0038 : CheckedFact 38 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 38) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 41) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0042 : CheckedFact 42 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 42) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0044 : CheckedFact 44 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 44) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0045 : CheckedFact 45 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 45) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0046 : CheckedFact 46 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 46) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0047 : CheckedFact 47 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 47) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0048 : CheckedFact 48 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 48) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0049 : CheckedFact 49 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 49) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0051 : CheckedFact 51 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 51) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0052 : CheckedFact 52 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 52) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0053 : CheckedFact 53 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 53) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0054 : CheckedFact 54 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 54) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0056 : CheckedFact 56 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 56) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 59) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0060 : CheckedFact 60 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 60) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0061 : CheckedFact 61 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 61) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 65) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0066 : CheckedFact 66 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 66) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0067 : CheckedFact 67 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 67) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0071 : CheckedFact 71 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 71) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0072 : CheckedFact 72 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 72) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0073 : CheckedFact 73 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 73) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 76) (positions := (1,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 82) (positions := (21,22))
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
    DistanceLeaf.checkWitness_sound (points := obligations 86) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0087 : CheckedFact 87 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 87) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0091 : CheckedFact 91 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 91) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0092 : CheckedFact 92 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 92) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0093 : CheckedFact 93 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 93) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0094 : CheckedFact 94 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 94) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 98) (positions := (1,3))
      (by decide +kernel) T contained

theorem checked_0100 : CheckedFact 100 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 100) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0101 : CheckedFact 101 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 101) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0102 : CheckedFact 102 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 102) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0103 : CheckedFact 103 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 103) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0108 : CheckedFact 108 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 108) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0109 : CheckedFact 109 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 109) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 112) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0113 : CheckedFact 113 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 113) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0114 : CheckedFact 114 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 114) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0115 : CheckedFact 115 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 115) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0116 : CheckedFact 116 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 116) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0117 : CheckedFact 117 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 117) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0118 : CheckedFact 118 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 118) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0119 : CheckedFact 119 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 119) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0120 : CheckedFact 120 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 120) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0121 : CheckedFact 121 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 121) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0122 : CheckedFact 122 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 122)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0123 : CheckedFact 123 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 123) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0124 : CheckedFact 124 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 124) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0125 : CheckedFact 125 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 125) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0126 : CheckedFact 126 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 126) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0129 : CheckedFact 129 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 129) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0130 : CheckedFact 130 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 130) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0131 : CheckedFact 131 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 131) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0132 : CheckedFact 132 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 132) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0133 : CheckedFact 133 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 133) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0134 : CheckedFact 134 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 134) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0135 : CheckedFact 135 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 135) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0136 : CheckedFact 136 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 136) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0137 : CheckedFact 137 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 137) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0138 : CheckedFact 138 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 138) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0139 : CheckedFact 139 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 139) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0140 : CheckedFact 140 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 140) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0142 : CheckedFact 142 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 142) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0143 : CheckedFact 143 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 143) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0144 : CheckedFact 144 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 144) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0145 : CheckedFact 145 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 145) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0146 : CheckedFact 146 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 146)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0147 : CheckedFact 147 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 147) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0148 : CheckedFact 148 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 148) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0149 : CheckedFact 149 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 149) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0150 : CheckedFact 150 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 150) (positions := (1,3))
      (by decide +kernel) T contained

theorem checked_0151 : CheckedFact 151 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 151) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0152 : CheckedFact 152 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 152) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0153 : CheckedFact 153 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 153) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0154 : CheckedFact 154 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 154) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0155 : CheckedFact 155 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 155) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0157 : CheckedFact 157 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 157) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0158 : CheckedFact 158 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 158) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0159 : CheckedFact 159 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 159) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0160 : CheckedFact 160 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 160) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0161 : CheckedFact 161 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 161) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0162 : CheckedFact 162 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 162) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0164 : CheckedFact 164 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 164)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0166 : CheckedFact 166 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 166) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0168 : CheckedFact 168 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 168) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0169 : CheckedFact 169 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 169) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0170 : CheckedFact 170 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 170) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0171 : CheckedFact 171 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 171) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0172 : CheckedFact 172 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 172) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0173 : CheckedFact 173 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 173) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0174 : CheckedFact 174 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 174) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0175 : CheckedFact 175 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 175) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0177 : CheckedFact 177 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 177)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0180 : CheckedFact 180 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 180) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0181 : CheckedFact 181 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 181) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0182 : CheckedFact 182 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 182) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0183 : CheckedFact 183 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 183) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0186 : CheckedFact 186 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 186) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0187 : CheckedFact 187 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 187) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0188 : CheckedFact 188 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 188) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0189 : CheckedFact 189 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 189) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0190 : CheckedFact 190 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 190) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0195 : CheckedFact 195 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 195) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0196 : CheckedFact 196 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 196) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0197 : CheckedFact 197 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 197) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0198 : CheckedFact 198 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 198) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0202 : CheckedFact 202 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 202) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0203 : CheckedFact 203 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 203) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0204 : CheckedFact 204 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 204) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0205 : CheckedFact 205 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 205) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0207 : CheckedFact 207 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 207) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0208 : CheckedFact 208 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 208) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0209 : CheckedFact 209 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 209) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0210 : CheckedFact 210 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 210) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0213 : CheckedFact 213 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 213) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0214 : CheckedFact 214 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 214) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0215 : CheckedFact 215 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 215) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0216 : CheckedFact 216 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 216) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0220 : CheckedFact 220 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 220) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0221 : CheckedFact 221 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 221) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0222 : CheckedFact 222 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 222) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0223 : CheckedFact 223 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 223) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0225 : CheckedFact 225 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 225) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0227 : CheckedFact 227 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 227) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0228 : CheckedFact 228 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 228) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0229 : CheckedFact 229 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 229) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0231 : CheckedFact 231 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 231) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0235 : CheckedFact 235 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 235) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0236 : CheckedFact 236 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 236) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0238 : CheckedFact 238 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 238) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0239 : CheckedFact 239 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 239) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0240 : CheckedFact 240 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 240) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0241 : CheckedFact 241 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 241) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0243 : CheckedFact 243 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 243) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0244 : CheckedFact 244 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 244) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0245 : CheckedFact 245 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 245) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0247 : CheckedFact 247 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 247)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0249 : CheckedFact 249 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 249) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0250 : CheckedFact 250 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 250) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0251 : CheckedFact 251 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 251) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0252 : CheckedFact 252 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 252) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0254 : CheckedFact 254 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 254)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0255 : CheckedFact 255 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 255) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0256 : CheckedFact 256 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 256) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0257 : CheckedFact 257 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 257) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0259 : CheckedFact 259 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 259) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0260 : CheckedFact 260 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 260) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0261 : CheckedFact 261 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 261) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0262 : CheckedFact 262 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 262) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0264 : CheckedFact 264 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 264) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0265 : CheckedFact 265 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 265) (positions := (22,23))
      (by decide +kernel) T contained

theorem checked_0266 : CheckedFact 266 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 266) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0267 : CheckedFact 267 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 267) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0268 : CheckedFact 268 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 268) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0270 : CheckedFact 270 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 270) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0272 : CheckedFact 272 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 272) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0273 : CheckedFact 273 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 273) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0274 : CheckedFact 274 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 274) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0276 : CheckedFact 276 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 276) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0278 : CheckedFact 278 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 278) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0279 : CheckedFact 279 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 279) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0282 : CheckedFact 282 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 282) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0284 : CheckedFact 284 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 284) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0285 : CheckedFact 285 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 285) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0286 : CheckedFact 286 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 286) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0287 : CheckedFact 287 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 287) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0289 : CheckedFact 289 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 289) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0291 : CheckedFact 291 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 291) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0292 : CheckedFact 292 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 292) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0293 : CheckedFact 293 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 293) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0295 : CheckedFact 295 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 295) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0297 : CheckedFact 297 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 297) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0299 : CheckedFact 299 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 299) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0300 : CheckedFact 300 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 300) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0301 : CheckedFact 301 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 301) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0304 : CheckedFact 304 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 304) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0305 : CheckedFact 305 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 305) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0306 : CheckedFact 306 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 306) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0307 : CheckedFact 307 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 307) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0310 : CheckedFact 310 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 310) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0311 : CheckedFact 311 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 311) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0312 : CheckedFact 312 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 312) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0313 : CheckedFact 313 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 313) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0314 : CheckedFact 314 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 314) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0315 : CheckedFact 315 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 315) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0316 : CheckedFact 316 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 316) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0317 : CheckedFact 317 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 317) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0318 : CheckedFact 318 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 318) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0320 : CheckedFact 320 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 320) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0321 : CheckedFact 321 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 321) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0322 : CheckedFact 322 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 322) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0323 : CheckedFact 323 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 323) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0325 : CheckedFact 325 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 325) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0326 : CheckedFact 326 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 326) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0327 : CheckedFact 327 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 327) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0329 : CheckedFact 329 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 329) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0330 : CheckedFact 330 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 330) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0332 : CheckedFact 332 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 332) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0333 : CheckedFact 333 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 333) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0335 : CheckedFact 335 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 335) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0336 : CheckedFact 336 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 336) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0337 : CheckedFact 337 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 337) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0339 : CheckedFact 339 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 339) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0341 : CheckedFact 341 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 341) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0342 : CheckedFact 342 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 342) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0344 : CheckedFact 344 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 344) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0345 : CheckedFact 345 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 345) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0347 : CheckedFact 347 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 347) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0349 : CheckedFact 349 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 349) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0350 : CheckedFact 350 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 350) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0351 : CheckedFact 351 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 351) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0352 : CheckedFact 352 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 352) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0355 : CheckedFact 355 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 355) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0356 : CheckedFact 356 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 356) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0357 : CheckedFact 357 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 357) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0358 : CheckedFact 358 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 358) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0360 : CheckedFact 360 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 360) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0361 : CheckedFact 361 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 361) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0362 : CheckedFact 362 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 362) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0363 : CheckedFact 363 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 363) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0364 : CheckedFact 364 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 364) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0365 : CheckedFact 365 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 365) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0366 : CheckedFact 366 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 366) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0367 : CheckedFact 367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 367) (positions := (2,5))
      (by decide +kernel) T contained

theorem checked_0368 : CheckedFact 368 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 368) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0369 : CheckedFact 369 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 369) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0370 : CheckedFact 370 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 370) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0376 : CheckedFact 376 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 376) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0378 : CheckedFact 378 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 378) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0379 : CheckedFact 379 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 379) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0380 : CheckedFact 380 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 380) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0381 : CheckedFact 381 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 381) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0382 : CheckedFact 382 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 382) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0383 : CheckedFact 383 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 383) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_0386 : CheckedFact 386 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 386) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0390 : CheckedFact 390 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 390) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0391 : CheckedFact 391 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 391) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0393 : CheckedFact 393 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 393) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0396 : CheckedFact 396 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 396) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0397 : CheckedFact 397 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 397) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0399 : CheckedFact 399 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 399) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0400 : CheckedFact 400 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 400) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0402 : CheckedFact 402 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 402) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0403 : CheckedFact 403 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 403) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0404 : CheckedFact 404 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 404) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0405 : CheckedFact 405 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 405) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0406 : CheckedFact 406 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 406) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0408 : CheckedFact 408 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 408) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0409 : CheckedFact 409 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 409) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0410 : CheckedFact 410 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 410) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0411 : CheckedFact 411 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 411) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0412 : CheckedFact 412 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 412) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0414 : CheckedFact 414 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 414) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0415 : CheckedFact 415 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 415) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0416 : CheckedFact 416 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 416) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0419 : CheckedFact 419 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 419) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0424 : CheckedFact 424 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 424) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0425 : CheckedFact 425 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 425) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0426 : CheckedFact 426 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 426) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0427 : CheckedFact 427 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 427) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0430 : CheckedFact 430 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 430) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0433 : CheckedFact 433 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 433) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0434 : CheckedFact 434 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 434) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0435 : CheckedFact 435 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 435) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0436 : CheckedFact 436 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 436) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0439 : CheckedFact 439 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 439) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0440 : CheckedFact 440 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 440) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0441 : CheckedFact 441 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 441) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0442 : CheckedFact 442 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 442) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0446 : CheckedFact 446 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 446) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0447 : CheckedFact 447 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 447) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0448 : CheckedFact 448 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 448) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0453 : CheckedFact 453 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 453) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_0454 : CheckedFact 454 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 454) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0455 : CheckedFact 455 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 455) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0456 : CheckedFact 456 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 456) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0457 : CheckedFact 457 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 457)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0467 : CheckedFact 467 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 467) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0468 : CheckedFact 468 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 468) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0469 : CheckedFact 469 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 469) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0470 : CheckedFact 470 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 470) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0479 : CheckedFact 479 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 479) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0480 : CheckedFact 480 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 480) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0481 : CheckedFact 481 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 481) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0482 : CheckedFact 482 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 482) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0483 : CheckedFact 483 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0006.c0006_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0491 : CheckedFact 491 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 491) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0492 : CheckedFact 492 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 492) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0493 : CheckedFact 493 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 493) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0494 : CheckedFact 494 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 494) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0496 : CheckedFact 496 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 496)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0509 : CheckedFact 509 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 509) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0510 : CheckedFact 510 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 510) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0513 : CheckedFact 513 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 513) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0514 : CheckedFact 514 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 514) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0515 : CheckedFact 515 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 515) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0516 : CheckedFact 516 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 516) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0518 : CheckedFact 518 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 518) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0521 : CheckedFact 521 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 521) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0522 : CheckedFact 522 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 522) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0523 : CheckedFact 523 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 523) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0524 : CheckedFact 524 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 524) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0527 : CheckedFact 527 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 527) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0528 : CheckedFact 528 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 528) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0529 : CheckedFact 529 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 529) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0530 : CheckedFact 530 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 530) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0538 : CheckedFact 538 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 538) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0539 : CheckedFact 539 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 539) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0552 : CheckedFact 552 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 552) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0553 : CheckedFact 553 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 553) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0554 : CheckedFact 554 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 554) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0555 : CheckedFact 555 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 555) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0570 : CheckedFact 570 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 570) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0571 : CheckedFact 571 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 571) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0572 : CheckedFact 572 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 572) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0573 : CheckedFact 573 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 573) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0575 : CheckedFact 575 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 575) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0576 : CheckedFact 576 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 576) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0577 : CheckedFact 577 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 577) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0578 : CheckedFact 578 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 578) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0579 : CheckedFact 579 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 579) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0581 : CheckedFact 581 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 581) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0582 : CheckedFact 582 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 582) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0583 : CheckedFact 583 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 583) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0584 : CheckedFact 584 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 584) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0585 : CheckedFact 585 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 585) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0591 : CheckedFact 591 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 591) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0592 : CheckedFact 592 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 592) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0593 : CheckedFact 593 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 593) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0616 : CheckedFact 616 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 616) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0617 : CheckedFact 617 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 617) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0618 : CheckedFact 618 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 618) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0632 : CheckedFact 632 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 632) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0634 : CheckedFact 634 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 634) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0637 : CheckedFact 637 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 637) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0638 : CheckedFact 638 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 638) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0639 : CheckedFact 639 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 639) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0641 : CheckedFact 641 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 641) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0642 : CheckedFact 642 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 642) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0643 : CheckedFact 643 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 643) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0645 : CheckedFact 645 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 645) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0671 : CheckedFact 671 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 671) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0686 : CheckedFact 686 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 686) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0687 : CheckedFact 687 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 687) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0690 : CheckedFact 690 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 690) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0704 : CheckedFact 704 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 704) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0705 : CheckedFact 705 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 705) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0706 : CheckedFact 706 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 706) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0707 : CheckedFact 707 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 707) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0708 : CheckedFact 708 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 708) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0714 : CheckedFact 714 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 714) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0715 : CheckedFact 715 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 715) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0716 : CheckedFact 716 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 716) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0717 : CheckedFact 717 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 717) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0724 : CheckedFact 724 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 724) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0725 : CheckedFact 725 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 725) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0726 : CheckedFact 726 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 726) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0728 : CheckedFact 728 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 728) (positions := (2,3))
      (by decide +kernel) T contained

#print axioms checked_0483
end HexagonCover.N7900.Arithmetic
