import HexagonCover.NBand.M8500_8700.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.Arithmetic.Run0007
open Common Semantics DistanceLeaf

theorem checked_1144 : CheckedFact 1144 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1144) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1148 : CheckedFact 1148 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1148) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1150 : CheckedFact 1150 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1150) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1151 : CheckedFact 1151 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1151) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1159 : CheckedFact 1159 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1159) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1161 : CheckedFact 1161 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1161) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1165 : CheckedFact 1165 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1165) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1166 : CheckedFact 1166 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1166) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1167 : CheckedFact 1167 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1167) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1168 : CheckedFact 1168 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1168) (positions := (0,5))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8500_8700.Arithmetic.Run0007
