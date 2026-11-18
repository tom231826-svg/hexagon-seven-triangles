import HexagonCover.NBand.M6900_7100.Semantics
import HexagonCover.NISubsetData.Batch0004
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.Arithmetic.Run0004
open Common Semantics DistanceLeaf

theorem checked_0585 : CheckedFact 585 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 585) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0586 : CheckedFact 586 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 586) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0587 : CheckedFact 587 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 587) (positions := (1,4))
      (by decide +kernel) T contained

theorem checked_0588 : CheckedFact 588 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 588) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_0597 : CheckedFact 597 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 597) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0598 : CheckedFact 598 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 598) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0615 : CheckedFact 615 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0004.c0001_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0630 : CheckedFact 630 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 630) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0634 : CheckedFact 634 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 634) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0635 : CheckedFact 635 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 635) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0637 : CheckedFact 637 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 637) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0656 : CheckedFact 656 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 656) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0657 : CheckedFact 657 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 657) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0658 : CheckedFact 658 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 658) (positions := (1,4))
      (by decide +kernel) T contained

theorem checked_0660 : CheckedFact 660 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 660) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0711 : CheckedFact 711 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 711) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0712 : CheckedFact 712 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 712) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0713 : CheckedFact 713 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 713) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0714 : CheckedFact 714 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 714) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0715 : CheckedFact 715 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 715)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0724 : CheckedFact 724 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 724) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0725 : CheckedFact 725 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 725) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0726 : CheckedFact 726 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 726) (positions := (1,4))
      (by decide +kernel) T contained

theorem checked_0736 : CheckedFact 736 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0004.c0002_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0756 : CheckedFact 756 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 756) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0757 : CheckedFact 757 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 757) (positions := (1,5))
      (by decide +kernel) T contained

theorem checked_0760 : CheckedFact 760 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 760) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0761 : CheckedFact 761 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 761) (positions := (1,5))
      (by decide +kernel) T contained

theorem checked_0764 : CheckedFact 764 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 764) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0765 : CheckedFact 765 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 765) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0766 : CheckedFact 766 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 766) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0767 : CheckedFact 767 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 767) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0768 : CheckedFact 768 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 768) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0773 : CheckedFact 773 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 773) (positions := (21,26))
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
    DistanceLeaf.checkWitness_sound (points := obligations 789) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0790 : CheckedFact 790 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 790) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0791 : CheckedFact 791 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0004.c0003_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0794 : CheckedFact 794 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 794) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0796 : CheckedFact 796 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 796) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0797 : CheckedFact 797 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0004.c0004_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0798 : CheckedFact 798 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 798) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0803 : CheckedFact 803 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 803) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0804 : CheckedFact 804 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 804) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0807 : CheckedFact 807 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 807) (positions := (5,6))
      (by decide +kernel) T contained

theorem checked_0808 : CheckedFact 808 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 808) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0810 : CheckedFact 810 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 810) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0811 : CheckedFact 811 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 811) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0813 : CheckedFact 813 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 813) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0814 : CheckedFact 814 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 814) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0816 : CheckedFact 816 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 816) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0817 : CheckedFact 817 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 817) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0819 : CheckedFact 819 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 819) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0821 : CheckedFact 821 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 821) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0823 : CheckedFact 823 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 823) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0831 : CheckedFact 831 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 831) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0832 : CheckedFact 832 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 832) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0833 : CheckedFact 833 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 833) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0834 : CheckedFact 834 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 834) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0837 : CheckedFact 837 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 837) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0838 : CheckedFact 838 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 838) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0839 : CheckedFact 839 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 839) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0840 : CheckedFact 840 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 840) (positions := (1,5))
      (by decide +kernel) T contained

theorem checked_0842 : CheckedFact 842 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 842) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0843 : CheckedFact 843 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 843) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0859 : CheckedFact 859 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 859) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0871 : CheckedFact 871 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 871) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0872 : CheckedFact 872 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 872) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0874 : CheckedFact 874 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 874) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0880 : CheckedFact 880 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 880) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0881 : CheckedFact 881 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 881) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0883 : CheckedFact 883 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0004.c0005_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0889 : CheckedFact 889 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 889) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0891 : CheckedFact 891 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 891) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0893 : CheckedFact 893 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 893) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0896 : CheckedFact 896 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 896) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0897 : CheckedFact 897 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 897) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0898 : CheckedFact 898 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 898) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0899 : CheckedFact 899 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 899) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0900 : CheckedFact 900 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 900) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0901 : CheckedFact 901 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 901) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0902 : CheckedFact 902 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 902) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0903 : CheckedFact 903 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 903) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0904 : CheckedFact 904 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 904) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0905 : CheckedFact 905 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 905) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0907 : CheckedFact 907 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 907) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0912 : CheckedFact 912 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 912) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0918 : CheckedFact 918 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 918) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0927 : CheckedFact 927 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0004.c0006_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0932 : CheckedFact 932 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 932) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0933 : CheckedFact 933 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 933) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0938 : CheckedFact 938 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 938) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0943 : CheckedFact 943 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 943) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0944 : CheckedFact 944 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 944) (positions := (0,6))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6900_7100.Arithmetic.Run0004
