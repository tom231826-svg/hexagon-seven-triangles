import HexagonCover.NBand.M6667_6700.Semantics
import HexagonCover.NISubsetData.Batch0002
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.Arithmetic.Run0005
open Common Semantics DistanceLeaf

theorem checked_0808 : CheckedFact 808 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 808) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0810 : CheckedFact 810 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 810) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0816 : CheckedFact 816 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0002.c0003_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0817 : CheckedFact 817 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 817) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0820 : CheckedFact 820 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 820) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0821 : CheckedFact 821 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0002.c0004_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0823 : CheckedFact 823 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 823) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0825 : CheckedFact 825 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 825) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0827 : CheckedFact 827 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 827) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0829 : CheckedFact 829 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 829) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0830 : CheckedFact 830 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 830) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0831 : CheckedFact 831 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 831) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0832 : CheckedFact 832 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 832) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0833 : CheckedFact 833 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 833) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0834 : CheckedFact 834 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 834) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0835 : CheckedFact 835 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 835) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0836 : CheckedFact 836 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 836) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0838 : CheckedFact 838 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 838) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0839 : CheckedFact 839 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 839) (positions := (2,5))
      (by decide +kernel) T contained

theorem checked_0840 : CheckedFact 840 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 840) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0843 : CheckedFact 843 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 843) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0845 : CheckedFact 845 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 845) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0846 : CheckedFact 846 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 846) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0847 : CheckedFact 847 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 847) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0848 : CheckedFact 848 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 848) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0849 : CheckedFact 849 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 849) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0850 : CheckedFact 850 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 850) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0851 : CheckedFact 851 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 851) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0852 : CheckedFact 852 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 852) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0854 : CheckedFact 854 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 854) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0855 : CheckedFact 855 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 855) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0856 : CheckedFact 856 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 856) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0858 : CheckedFact 858 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 858) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0859 : CheckedFact 859 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 859) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0862 : CheckedFact 862 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 862) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0864 : CheckedFact 864 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 864) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0865 : CheckedFact 865 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 865) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0866 : CheckedFact 866 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 866) (positions := (21,25))
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

theorem checked_0873 : CheckedFact 873 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 873) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0874 : CheckedFact 874 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 874) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0875 : CheckedFact 875 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 875) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0876 : CheckedFact 876 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 876) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0877 : CheckedFact 877 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 877) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0878 : CheckedFact 878 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 878) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0879 : CheckedFact 879 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 879) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0880 : CheckedFact 880 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 880) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0883 : CheckedFact 883 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 883) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0884 : CheckedFact 884 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 884) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0889 : CheckedFact 889 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 889) (positions := (25,26))
      (by decide +kernel) T contained

theorem checked_0894 : CheckedFact 894 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 894) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0895 : CheckedFact 895 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 895) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0896 : CheckedFact 896 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 896) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0899 : CheckedFact 899 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 899) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0900 : CheckedFact 900 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 900) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0902 : CheckedFact 902 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 902) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0908 : CheckedFact 908 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 908) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0909 : CheckedFact 909 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 909) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0911 : CheckedFact 911 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 911) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0912 : CheckedFact 912 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 912) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0913 : CheckedFact 913 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 913) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0914 : CheckedFact 914 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 914) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0915 : CheckedFact 915 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 915) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_0916 : CheckedFact 916 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 916) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0917 : CheckedFact 917 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 917) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0918 : CheckedFact 918 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 918) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0919 : CheckedFact 919 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 919) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0921 : CheckedFact 921 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 921) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0922 : CheckedFact 922 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 922) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0923 : CheckedFact 923 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 923) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0924 : CheckedFact 924 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 924) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0931 : CheckedFact 931 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 931) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0932 : CheckedFact 932 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 932) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0938 : CheckedFact 938 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 938) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_0945 : CheckedFact 945 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 945) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0956 : CheckedFact 956 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 956) (positions := (23,26))
      (by decide +kernel) T contained

theorem checked_0958 : CheckedFact 958 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 958) (positions := (22,26))
      (by decide +kernel) T contained

theorem checked_0966 : CheckedFact 966 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 966) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0967 : CheckedFact 967 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 967) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0968 : CheckedFact 968 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 968) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0969 : CheckedFact 969 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 969) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0971 : CheckedFact 971 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 971) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0972 : CheckedFact 972 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 972) (positions := (22,23))
      (by decide +kernel) T contained

theorem checked_0973 : CheckedFact 973 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 973) (positions := (22,26))
      (by decide +kernel) T contained

theorem checked_0975 : CheckedFact 975 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 975) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0976 : CheckedFact 976 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 976) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0977 : CheckedFact 977 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 977) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0980 : CheckedFact 980 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 980) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0981 : CheckedFact 981 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 981) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0982 : CheckedFact 982 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 982) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0983 : CheckedFact 983 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 983) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0984 : CheckedFact 984 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 984) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0986 : CheckedFact 986 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 986) (positions := (25,26))
      (by decide +kernel) T contained

theorem checked_0992 : CheckedFact 992 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 992) (positions := (0,4))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6667_6700.Arithmetic.Run0005
