import HexagonCover.NBand.M7100_7300.Semantics
import HexagonCover.NISubsetData.Batch0005
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.Arithmetic.Run0004
open Common Semantics DistanceLeaf

theorem checked_0574 : CheckedFact 574 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0005.c0003_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0576 : CheckedFact 576 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0005.c0004_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0579 : CheckedFact 579 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 579) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0580 : CheckedFact 580 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 580) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0581 : CheckedFact 581 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 581) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0582 : CheckedFact 582 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 582) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0586 : CheckedFact 586 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 586) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0587 : CheckedFact 587 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 587) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0588 : CheckedFact 588 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 588) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0590 : CheckedFact 590 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 590) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0592 : CheckedFact 592 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 592) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0593 : CheckedFact 593 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 593) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0600 : CheckedFact 600 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 600) (positions := (2,8))
      (by decide +kernel) T contained

theorem checked_0601 : CheckedFact 601 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 601) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0602 : CheckedFact 602 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 602) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0603 : CheckedFact 603 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 603) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0607 : CheckedFact 607 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 607) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0608 : CheckedFact 608 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 608) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0609 : CheckedFact 609 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 609) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0611 : CheckedFact 611 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 611) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0618 : CheckedFact 618 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 618) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0623 : CheckedFact 623 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 623) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0626 : CheckedFact 626 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 626) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0631 : CheckedFact 631 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 631) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0635 : CheckedFact 635 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 635) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0636 : CheckedFact 636 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 636) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0642 : CheckedFact 642 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 642) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0643 : CheckedFact 643 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 643) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0644 : CheckedFact 644 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 644) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0646 : CheckedFact 646 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 646) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0650 : CheckedFact 650 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 650) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0656 : CheckedFact 656 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 656) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0657 : CheckedFact 657 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 657) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0658 : CheckedFact 658 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 658) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0661 : CheckedFact 661 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 661) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_0662 : CheckedFact 662 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 662) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0663 : CheckedFact 663 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 663) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0665 : CheckedFact 665 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 665)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0681 : CheckedFact 681 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 681) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0682 : CheckedFact 682 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 682) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0683 : CheckedFact 683 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 683) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0684 : CheckedFact 684 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 684) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0687 : CheckedFact 687 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 687) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0688 : CheckedFact 688 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 688) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0689 : CheckedFact 689 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 689) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0696 : CheckedFact 696 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0005.c0005_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0697 : CheckedFact 697 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 697) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0698 : CheckedFact 698 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 698) (positions := (2,5))
      (by decide +kernel) T contained

theorem checked_0699 : CheckedFact 699 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 699) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0700 : CheckedFact 700 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 700) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0702 : CheckedFact 702 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 702)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0705 : CheckedFact 705 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 705) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0708 : CheckedFact 708 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 708) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0709 : CheckedFact 709 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 709) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0719 : CheckedFact 719 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 719) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0720 : CheckedFact 720 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 720) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0736 : CheckedFact 736 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 736) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0737 : CheckedFact 737 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 737) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0738 : CheckedFact 738 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 738) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0751 : CheckedFact 751 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 751) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0762 : CheckedFact 762 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 762) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0763 : CheckedFact 763 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 763) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0764 : CheckedFact 764 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 764) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0766 : CheckedFact 766 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 766) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0767 : CheckedFact 767 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 767) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0768 : CheckedFact 768 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 768) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0773 : CheckedFact 773 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 773) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0774 : CheckedFact 774 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 774) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0775 : CheckedFact 775 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 775) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0776 : CheckedFact 776 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 776) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0779 : CheckedFact 779 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 779) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0780 : CheckedFact 780 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 780) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0781 : CheckedFact 781 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 781) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0782 : CheckedFact 782 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 782) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0785 : CheckedFact 785 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 785) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0786 : CheckedFact 786 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 786) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0787 : CheckedFact 787 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 787) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0788 : CheckedFact 788 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 788) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0790 : CheckedFact 790 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 790) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0791 : CheckedFact 791 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 791) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0796 : CheckedFact 796 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 796) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0797 : CheckedFact 797 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 797) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0798 : CheckedFact 798 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 798) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0799 : CheckedFact 799 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 799) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0800 : CheckedFact 800 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 800) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0801 : CheckedFact 801 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 801) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0802 : CheckedFact 802 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 802) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0808 : CheckedFact 808 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 808) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0811 : CheckedFact 811 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 811) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0815 : CheckedFact 815 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 815) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0816 : CheckedFact 816 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 816) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0818 : CheckedFact 818 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 818) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0819 : CheckedFact 819 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 819) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0822 : CheckedFact 822 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 822) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0824 : CheckedFact 824 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 824) (positions := (21,25))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7100_7300.Arithmetic.Run0004
