import HexagonCover.NBand.M7700_7900.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.Arithmetic.Run0000
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

theorem checked_0027 : CheckedFact 27 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 27) (positions := (0,3))
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

theorem checked_0043 : CheckedFact 43 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 43) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0044 : CheckedFact 44 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 44) (positions := (0,3))
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

theorem checked_0050 : CheckedFact 50 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 50) (positions := (2,3))
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

theorem checked_0067 : CheckedFact 67 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 67) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 70) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0071 : CheckedFact 71 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 71) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0072 : CheckedFact 72 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 72) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 75) (positions := (21,22))
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
    DistanceLeaf.checkWitness_sound (points := obligations 82) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 86) (positions := (1,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 91) (positions := (1,3))
      (by decide +kernel) T contained

theorem checked_0092 : CheckedFact 92 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 92) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 108) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0109 : CheckedFact 109 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 109) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0110 : CheckedFact 110 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 110)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0111 : CheckedFact 111 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 111) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0112 : CheckedFact 112 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 112) (positions := (0,3))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7700_7900.Arithmetic.Run0000
