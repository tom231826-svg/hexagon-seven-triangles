import HexagonCover.SmallestN.Semantics
import HexagonCover.PointSegmentLeaf
import HexagonCover.NISubsetData.Batch0000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.SmallestN.Arithmetic
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

theorem checked_0005 : CheckedFact 5 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 5)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

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
    DistanceLeaf.checkWitness_sound (points := obligations 37) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0039 : CheckedFact 39 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 39) (positions := (2,3))
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

theorem checked_0043 : CheckedFact 43 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 43) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 49) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 56) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 63) (positions := (2,3))
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

theorem checked_0068 : CheckedFact 68 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 68) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 71) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0072 : CheckedFact 72 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 72) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0073 : CheckedFact 73 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 73) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 77) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0078 : CheckedFact 78 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 78) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0079 : CheckedFact 79 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 79) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0083 : CheckedFact 83 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 83) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0084 : CheckedFact 84 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 84) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 87) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0088 : CheckedFact 88 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 88) (positions := (1,3))
      (by decide +kernel) T contained

theorem checked_0090 : CheckedFact 90 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 90) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0091 : CheckedFact 91 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 91) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0093 : CheckedFact 93 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 93) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0094 : CheckedFact 94 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 94) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0095 : CheckedFact 95 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 95) (positions := (21,22))
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
    DistanceLeaf.checkWitness_sound (points := obligations 100) (positions := (21,22))
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

theorem checked_0104 : CheckedFact 104 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 104) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0105 : CheckedFact 105 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 105) (positions := (21,22))
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
    DistanceLeaf.checkWitness_sound (points := obligations 116) (positions := (1,3))
      (by decide +kernel) T contained

theorem checked_0118 : CheckedFact 118 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 118) (positions := (0,3))
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

theorem checked_0126 : CheckedFact 126 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 126) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0127 : CheckedFact 127 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 127) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0128 : CheckedFact 128 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 128) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0129 : CheckedFact 129 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 129) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0130 : CheckedFact 130 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 130) (positions := (2,3))
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
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 140)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

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

theorem checked_0147 : CheckedFact 147 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 147) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0148 : CheckedFact 148 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 148) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0149 : CheckedFact 149 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 149) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0150 : CheckedFact 150 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 150) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0151 : CheckedFact 151 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 151) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0152 : CheckedFact 152 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 152) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0153 : CheckedFact 153 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 153) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0154 : CheckedFact 154 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 154) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0155 : CheckedFact 155 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 155) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0156 : CheckedFact 156 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 156) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0157 : CheckedFact 157 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 157) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0158 : CheckedFact 158 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 158) (positions := (21,22))
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

theorem checked_0163 : CheckedFact 163 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 163) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0164 : CheckedFact 164 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 164)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0165 : CheckedFact 165 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 165) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0166 : CheckedFact 166 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 166) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0167 : CheckedFact 167 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 167) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0168 : CheckedFact 168 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 168) (positions := (1,3))
      (by decide +kernel) T contained

theorem checked_0169 : CheckedFact 169 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 169) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0170 : CheckedFact 170 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 170) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0171 : CheckedFact 171 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 171) (positions := (22,24))
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

theorem checked_0176 : CheckedFact 176 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 176) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0178 : CheckedFact 178 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 178) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0179 : CheckedFact 179 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 179) (positions := (0,3))
      (by decide +kernel) T contained

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
    DistanceLeaf.checkWitness_sound (points := obligations 182) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0184 : CheckedFact 184 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 184) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0185 : CheckedFact 185 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 185) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0186 : CheckedFact 186 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 186) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0187 : CheckedFact 187 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 187) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0190 : CheckedFact 190 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 190) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0191 : CheckedFact 191 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 191) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0192 : CheckedFact 192 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 192) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0193 : CheckedFact 193 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 193) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0195 : CheckedFact 195 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 195)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0198 : CheckedFact 198 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 198) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0199 : CheckedFact 199 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 199) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0200 : CheckedFact 200 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 200) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0201 : CheckedFact 201 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 201) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0202 : CheckedFact 202 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 202) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0203 : CheckedFact 203 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 203) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0205 : CheckedFact 205 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 205) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0206 : CheckedFact 206 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 206) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0207 : CheckedFact 207 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 207) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0208 : CheckedFact 208 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 208) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0209 : CheckedFact 209 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 209) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0210 : CheckedFact 210 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 210) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0211 : CheckedFact 211 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 211) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0212 : CheckedFact 212 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 212) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0213 : CheckedFact 213 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 213) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0216 : CheckedFact 216 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 216) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0217 : CheckedFact 217 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 217) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0218 : CheckedFact 218 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 218) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0220 : CheckedFact 220 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 220) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0222 : CheckedFact 222 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 222) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0223 : CheckedFact 223 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 223) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0224 : CheckedFact 224 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 224) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0226 : CheckedFact 226 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 226) (positions := (0,3))
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

theorem checked_0232 : CheckedFact 232 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 232) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0233 : CheckedFact 233 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 233) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0234 : CheckedFact 234 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 234) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0236 : CheckedFact 236 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 236) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0237 : CheckedFact 237 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 237) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0238 : CheckedFact 238 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 238) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0239 : CheckedFact 239 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 239) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0242 : CheckedFact 242 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 242) (positions := (0,3))
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

theorem checked_0246 : CheckedFact 246 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 246) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0247 : CheckedFact 247 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 247) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0248 : CheckedFact 248 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 248) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0250 : CheckedFact 250 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 250)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0253 : CheckedFact 253 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 253) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0254 : CheckedFact 254 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 254) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0255 : CheckedFact 255 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 255) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0256 : CheckedFact 256 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 256) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0258 : CheckedFact 258 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 258) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0259 : CheckedFact 259 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 259) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0261 : CheckedFact 261 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 261) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0262 : CheckedFact 262 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 262) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0265 : CheckedFact 265 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 265) (positions := (0,3))
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

theorem checked_0271 : CheckedFact 271 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 271) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0273 : CheckedFact 273 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 273) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0274 : CheckedFact 274 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 274) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0275 : CheckedFact 275 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 275) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0277 : CheckedFact 277 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 277) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0281 : CheckedFact 281 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 281) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0282 : CheckedFact 282 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 282) (positions := (0,3))
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

theorem checked_0288 : CheckedFact 288 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 288) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0291 : CheckedFact 291 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 291) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0292 : CheckedFact 292 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 292) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0293 : CheckedFact 293 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 293) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0294 : CheckedFact 294 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 294) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0297 : CheckedFact 297 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 297) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0298 : CheckedFact 298 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 298) (positions := (0,3))
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

theorem checked_0302 : CheckedFact 302 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 302) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0303 : CheckedFact 303 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 303) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0305 : CheckedFact 305 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 305) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0306 : CheckedFact 306 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 306) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0308 : CheckedFact 308 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 308) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0309 : CheckedFact 309 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 309) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0310 : CheckedFact 310 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 310) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0312 : CheckedFact 312 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 312) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0314 : CheckedFact 314 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 314) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0315 : CheckedFact 315 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 315) (positions := (0,3))
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

theorem checked_0322 : CheckedFact 322 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 322) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0323 : CheckedFact 323 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 323) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0324 : CheckedFact 324 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 324) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0325 : CheckedFact 325 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 325) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0328 : CheckedFact 328 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 328) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0329 : CheckedFact 329 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 329) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0330 : CheckedFact 330 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 330) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0331 : CheckedFact 331 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 331) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0333 : CheckedFact 333 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 333) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0334 : CheckedFact 334 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 334) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0335 : CheckedFact 335 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 335) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0336 : CheckedFact 336 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 336) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0337 : CheckedFact 337 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 337) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0338 : CheckedFact 338 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 338) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0339 : CheckedFact 339 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 339) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0340 : CheckedFact 340 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 340) (positions := (2,5))
      (by decide +kernel) T contained

theorem checked_0341 : CheckedFact 341 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 341) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0342 : CheckedFact 342 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 342) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0343 : CheckedFact 343 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 343) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0349 : CheckedFact 349 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 349) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0351 : CheckedFact 351 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 351) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0352 : CheckedFact 352 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 352) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0353 : CheckedFact 353 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 353) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0354 : CheckedFact 354 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 354) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0355 : CheckedFact 355 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 355) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0356 : CheckedFact 356 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 356) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_0357 : CheckedFact 357 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 357) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0359 : CheckedFact 359 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 359) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0360 : CheckedFact 360 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 360) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0361 : CheckedFact 361 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 361) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0366 : CheckedFact 366 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 366) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0367 : CheckedFact 367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 367) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0368 : CheckedFact 368 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 368) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0369 : CheckedFact 369 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 369) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0371 : CheckedFact 371 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 371) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0372 : CheckedFact 372 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 372) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0373 : CheckedFact 373 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 373) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0374 : CheckedFact 374 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 374) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0375 : CheckedFact 375 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 375) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0376 : CheckedFact 376 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 376) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0377 : CheckedFact 377 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 377) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0378 : CheckedFact 378 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 378) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0379 : CheckedFact 379 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 379) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0381 : CheckedFact 381 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 381) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0383 : CheckedFact 383 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 383) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0384 : CheckedFact 384 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 384) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0385 : CheckedFact 385 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 385) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0388 : CheckedFact 388 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 388) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0391 : CheckedFact 391 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 391) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_0392 : CheckedFact 392 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 392) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0393 : CheckedFact 393 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 393) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0394 : CheckedFact 394 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 394) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0398 : CheckedFact 398 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 398) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0399 : CheckedFact 399 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 399) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0400 : CheckedFact 400 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 400) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0401 : CheckedFact 401 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 401) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0402 : CheckedFact 402 where
  excluded T contained hNI := by
    apply NISubsetData.Batch0000.c0000_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0405 : CheckedFact 405 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 405) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0406 : CheckedFact 406 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 406) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0407 : CheckedFact 407 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 407) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0408 : CheckedFact 408 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 408) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0409 : CheckedFact 409 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 409)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0415 : CheckedFact 415 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 415) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0416 : CheckedFact 416 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 416) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0420 : CheckedFact 420 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 420) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0421 : CheckedFact 421 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 421) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0422 : CheckedFact 422 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 422) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0424 : CheckedFact 424 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 424) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0429 : CheckedFact 429 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 429) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0430 : CheckedFact 430 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 430) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0431 : CheckedFact 431 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 431) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0432 : CheckedFact 432 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 432) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0434 : CheckedFact 434 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 434)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0436 : CheckedFact 436 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 436) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0437 : CheckedFact 437 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 437) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0438 : CheckedFact 438 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 438) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0439 : CheckedFact 439 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 439) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0440 : CheckedFact 440 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 440) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0443 : CheckedFact 443 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 443) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0445 : CheckedFact 445 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 445) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0446 : CheckedFact 446 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 446) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0447 : CheckedFact 447 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 447) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0448 : CheckedFact 448 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 448) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0449 : CheckedFact 449 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 449) (positions := (21,24))
      (by decide +kernel) T contained

#print axioms checked_0402
end HexagonCover.SmallestN.Arithmetic
