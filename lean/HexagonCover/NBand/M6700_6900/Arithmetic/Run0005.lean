import HexagonCover.NBand.M6700_6900.Semantics
import HexagonCover.NISubsetData.Batch0003
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.Arithmetic.Run0005
open Common Semantics DistanceLeaf

theorem checked_0757 : CheckedFact 757 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 757) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0762 : CheckedFact 762 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 762) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0766 : CheckedFact 766 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 766) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0767 : CheckedFact 767 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 767) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0768 : CheckedFact 768 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 768) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0770 : CheckedFact 770 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 770) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0779 : CheckedFact 779 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 779) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0780 : CheckedFact 780 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 780) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0781 : CheckedFact 781 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 781) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0783 : CheckedFact 783 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 783) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0787 : CheckedFact 787 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 787) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0788 : CheckedFact 788 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 788) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0789 : CheckedFact 789 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 789) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0790 : CheckedFact 790 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0003.c0001_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0791 : CheckedFact 791 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 791) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0792 : CheckedFact 792 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 792) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0793 : CheckedFact 793 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 793) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0794 : CheckedFact 794 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 794) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0796 : CheckedFact 796 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 796) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0797 : CheckedFact 797 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 797) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0798 : CheckedFact 798 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 798) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0802 : CheckedFact 802 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 802) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0803 : CheckedFact 803 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 803) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0804 : CheckedFact 804 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 804) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0808 : CheckedFact 808 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0003.c0002_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0810 : CheckedFact 810 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0003.c0003_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0812 : CheckedFact 812 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 812) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0813 : CheckedFact 813 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 813) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0815 : CheckedFact 815 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 815) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0822 : CheckedFact 822 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 822) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0823 : CheckedFact 823 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 823) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0825 : CheckedFact 825 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 825) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0826 : CheckedFact 826 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 826) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0827 : CheckedFact 827 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 827) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0831 : CheckedFact 831 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 831) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0832 : CheckedFact 832 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 832) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0834 : CheckedFact 834 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 834) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0835 : CheckedFact 835 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 835) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0836 : CheckedFact 836 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 836) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0840 : CheckedFact 840 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 840) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0841 : CheckedFact 841 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 841) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0843 : CheckedFact 843 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 843) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0844 : CheckedFact 844 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 844) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0845 : CheckedFact 845 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 845) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0847 : CheckedFact 847 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 847) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0848 : CheckedFact 848 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 848) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0850 : CheckedFact 850 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 850) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0851 : CheckedFact 851 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 851) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0852 : CheckedFact 852 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 852) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0853 : CheckedFact 853 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 853) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0854 : CheckedFact 854 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 854) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0855 : CheckedFact 855 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 855) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0859 : CheckedFact 859 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 859) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0860 : CheckedFact 860 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 860) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0861 : CheckedFact 861 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 861) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0862 : CheckedFact 862 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 862) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0863 : CheckedFact 863 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 863) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0864 : CheckedFact 864 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 864) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0873 : CheckedFact 873 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 873) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0874 : CheckedFact 874 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 874) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0875 : CheckedFact 875 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 875) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0879 : CheckedFact 879 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 879) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0880 : CheckedFact 880 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 880) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0881 : CheckedFact 881 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 881) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0883 : CheckedFact 883 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 883) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0884 : CheckedFact 884 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 884) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0885 : CheckedFact 885 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 885) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0891 : CheckedFact 891 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 891) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0892 : CheckedFact 892 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 892) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0893 : CheckedFact 893 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 893) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0895 : CheckedFact 895 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 895) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0896 : CheckedFact 896 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 896) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0897 : CheckedFact 897 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 897) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0898 : CheckedFact 898 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 898) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0899 : CheckedFact 899 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 899) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0900 : CheckedFact 900 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 900) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0901 : CheckedFact 901 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 901) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0902 : CheckedFact 902 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 902) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0909 : CheckedFact 909 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 909) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0910 : CheckedFact 910 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 910) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0911 : CheckedFact 911 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 911) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0912 : CheckedFact 912 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 912) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0913 : CheckedFact 913 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 913) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0914 : CheckedFact 914 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 914) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0915 : CheckedFact 915 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 915) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0916 : CheckedFact 916 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 916) (positions := (0,5))
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
    DistanceLeaf.checkWitness_sound (points := obligations 923) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0924 : CheckedFact 924 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 924) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0925 : CheckedFact 925 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 925) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0926 : CheckedFact 926 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 926) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0927 : CheckedFact 927 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 927) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0928 : CheckedFact 928 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 928) (positions := (0,5))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6700_6900.Arithmetic.Run0005
