import HexagonCover.NBand.M7300_7500.Semantics
import HexagonCover.NISubsetData.Batch0006
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.Arithmetic.Run0005
open Common Semantics DistanceLeaf

theorem checked_0779 : CheckedFact 779 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 779) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0780 : CheckedFact 780 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 780) (positions := (1,5))
      (by decide +kernel) T contained

theorem checked_0785 : CheckedFact 785 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 785) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0786 : CheckedFact 786 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 786) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0789 : CheckedFact 789 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 789) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0790 : CheckedFact 790 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 790) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0791 : CheckedFact 791 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 791) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0792 : CheckedFact 792 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 792) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0793 : CheckedFact 793 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 793) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0801 : CheckedFact 801 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 801) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0802 : CheckedFact 802 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 802) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0803 : CheckedFact 803 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 803) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0804 : CheckedFact 804 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 804) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0805 : CheckedFact 805 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 805) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0806 : CheckedFact 806 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 806) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0811 : CheckedFact 811 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 811) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0821 : CheckedFact 821 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 821) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0831 : CheckedFact 831 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 831) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0836 : CheckedFact 836 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0006.c0000_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0843 : CheckedFact 843 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 843) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0850 : CheckedFact 850 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 850) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0851 : CheckedFact 851 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 851) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0852 : CheckedFact 852 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 852) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0853 : CheckedFact 853 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 853) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0854 : CheckedFact 854 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 854) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0855 : CheckedFact 855 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 855) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0858 : CheckedFact 858 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 858) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0879 : CheckedFact 879 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 879) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0880 : CheckedFact 880 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 880) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0881 : CheckedFact 881 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 881) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0882 : CheckedFact 882 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 882) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0897 : CheckedFact 897 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 897) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0905 : CheckedFact 905 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 905)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 5 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0915 : CheckedFact 915 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 915) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0916 : CheckedFact 916 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 916) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0918 : CheckedFact 918 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 918) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0919 : CheckedFact 919 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 919) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0921 : CheckedFact 921 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 921) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0922 : CheckedFact 922 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 922) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0923 : CheckedFact 923 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 923) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0933 : CheckedFact 933 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 933) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0934 : CheckedFact 934 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 934) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0945 : CheckedFact 945 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 945) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0952 : CheckedFact 952 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 952) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0974 : CheckedFact 974 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 974) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0985 : CheckedFact 985 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 985) (positions := (24,26))
      (by decide +kernel) T contained

theorem checked_1024 : CheckedFact 1024 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1024)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 6 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1027 : CheckedFact 1027 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0006.c0001_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

end HexagonCover.NBand.M7300_7500.Arithmetic.Run0005
