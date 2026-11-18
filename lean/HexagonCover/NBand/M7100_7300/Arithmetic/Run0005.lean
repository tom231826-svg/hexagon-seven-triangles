import HexagonCover.NBand.M7100_7300.Semantics
import HexagonCover.NISubsetData.Batch0005
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.Arithmetic.Run0005
open Common Semantics DistanceLeaf

theorem checked_0825 : CheckedFact 825 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 825) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0826 : CheckedFact 826 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 826) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0837 : CheckedFact 837 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0005.c0006_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0859 : CheckedFact 859 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 859) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0863 : CheckedFact 863 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 863) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0864 : CheckedFact 864 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 864) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0867 : CheckedFact 867 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 867) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0868 : CheckedFact 868 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 868) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0869 : CheckedFact 869 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 869) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0870 : CheckedFact 870 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 870) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0872 : CheckedFact 872 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 872) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0873 : CheckedFact 873 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 873) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0895 : CheckedFact 895 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 895) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0896 : CheckedFact 896 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 896) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0898 : CheckedFact 898 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 898) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0899 : CheckedFact 899 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 899) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0903 : CheckedFact 903 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 903) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0904 : CheckedFact 904 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 904) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0908 : CheckedFact 908 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 908) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0909 : CheckedFact 909 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 909) (positions := (0,5))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7100_7300.Arithmetic.Run0005
