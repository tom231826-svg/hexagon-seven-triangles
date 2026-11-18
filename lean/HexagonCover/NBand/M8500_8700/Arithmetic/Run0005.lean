import HexagonCover.NBand.M8500_8700.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.Arithmetic.Run0005
open Common Semantics DistanceLeaf

theorem checked_0663 : CheckedFact 663 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 663) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0665 : CheckedFact 665 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 665) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0667 : CheckedFact 667 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 667) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0669 : CheckedFact 669 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 669) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0671 : CheckedFact 671 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 671) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0672 : CheckedFact 672 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 672) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0675 : CheckedFact 675 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 675) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0678 : CheckedFact 678 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 678) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0679 : CheckedFact 679 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 679) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0680 : CheckedFact 680 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 680) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0681 : CheckedFact 681 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 681) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0687 : CheckedFact 687 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 687)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 5 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0694 : CheckedFact 694 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 694) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0695 : CheckedFact 695 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 695) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0696 : CheckedFact 696 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 696) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0697 : CheckedFact 697 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 697) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0698 : CheckedFact 698 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 698)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0705 : CheckedFact 705 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 705) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0714 : CheckedFact 714 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 714) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0715 : CheckedFact 715 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 715) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0716 : CheckedFact 716 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 716) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0717 : CheckedFact 717 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 717) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0721 : CheckedFact 721 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 721) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0722 : CheckedFact 722 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 722) (positions := (2,8))
      (by decide +kernel) T contained

theorem checked_0725 : CheckedFact 725 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 725) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0727 : CheckedFact 727 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 727) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0729 : CheckedFact 729 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 729) (positions := (3,4))
      (by decide +kernel) T contained

theorem checked_0730 : CheckedFact 730 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 730) (positions := (3,4))
      (by decide +kernel) T contained

theorem checked_0733 : CheckedFact 733 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 733) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0734 : CheckedFact 734 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 734) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0736 : CheckedFact 736 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 736) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0740 : CheckedFact 740 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 740) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0741 : CheckedFact 741 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 741) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0742 : CheckedFact 742 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 742) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0743 : CheckedFact 743 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 743) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0744 : CheckedFact 744 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 744) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0746 : CheckedFact 746 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 746) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0747 : CheckedFact 747 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 747) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0748 : CheckedFact 748 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 748) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0752 : CheckedFact 752 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 752) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0753 : CheckedFact 753 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 753) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0754 : CheckedFact 754 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 754) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0762 : CheckedFact 762 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 762) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0763 : CheckedFact 763 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 763) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0764 : CheckedFact 764 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 764) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0765 : CheckedFact 765 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 765)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0767 : CheckedFact 767 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 767) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0768 : CheckedFact 768 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 768) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0769 : CheckedFact 769 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 769) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0771 : CheckedFact 771 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 771) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0773 : CheckedFact 773 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 773) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0774 : CheckedFact 774 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 774) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0775 : CheckedFact 775 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 775) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0776 : CheckedFact 776 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 776) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0790 : CheckedFact 790 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 790) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0791 : CheckedFact 791 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 791) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0794 : CheckedFact 794 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 794) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0795 : CheckedFact 795 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 795) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0796 : CheckedFact 796 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 796) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0801 : CheckedFact 801 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 801) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0802 : CheckedFact 802 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 802) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0803 : CheckedFact 803 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 803) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0804 : CheckedFact 804 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 804) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0808 : CheckedFact 808 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 808) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0809 : CheckedFact 809 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 809) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0810 : CheckedFact 810 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 810) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0811 : CheckedFact 811 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 811) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0814 : CheckedFact 814 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 814) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0815 : CheckedFact 815 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 815) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0816 : CheckedFact 816 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 816) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0817 : CheckedFact 817 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 817) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0820 : CheckedFact 820 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 820) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0821 : CheckedFact 821 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 821) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0822 : CheckedFact 822 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 822) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0823 : CheckedFact 823 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 823) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0841 : CheckedFact 841 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 841) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0842 : CheckedFact 842 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 842) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0866 : CheckedFact 866 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 866) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0867 : CheckedFact 867 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 867) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0869 : CheckedFact 869 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 869) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0870 : CheckedFact 870 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 870) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0871 : CheckedFact 871 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 871) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0872 : CheckedFact 872 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 872) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0874 : CheckedFact 874 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 874) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0877 : CheckedFact 877 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 877) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0886 : CheckedFact 886 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 886) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0887 : CheckedFact 887 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 887) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0888 : CheckedFact 888 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 888) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0890 : CheckedFact 890 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 890) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0892 : CheckedFact 892 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 892) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0893 : CheckedFact 893 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 893) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0894 : CheckedFact 894 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 894) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0895 : CheckedFact 895 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 895) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0901 : CheckedFact 901 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 901) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0902 : CheckedFact 902 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 902) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0903 : CheckedFact 903 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 903) (positions := (0,6))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8500_8700.Arithmetic.Run0005
