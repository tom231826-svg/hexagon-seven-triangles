import HexagonCover.NBand.M7500_7700.Semantics
import HexagonCover.NISubsetData.Batch0006
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.Arithmetic.Run0004
open Common Semantics DistanceLeaf

theorem checked_0556 : CheckedFact 556 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 556) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0557 : CheckedFact 557 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 557) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0558 : CheckedFact 558 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 558) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0564 : CheckedFact 564 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 564) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0565 : CheckedFact 565 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 565) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0566 : CheckedFact 566 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 566) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0567 : CheckedFact 567 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 567) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0568 : CheckedFact 568 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 568) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0569 : CheckedFact 569 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0006.c0004_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0573 : CheckedFact 573 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 573) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0574 : CheckedFact 574 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 574) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0575 : CheckedFact 575 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 575)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 4 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0576 : CheckedFact 576 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 576) (positions := (24,26))
      (by decide +kernel) T contained

theorem checked_0583 : CheckedFact 583 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 583) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0584 : CheckedFact 584 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 584) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0586 : CheckedFact 586 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 586) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0587 : CheckedFact 587 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 587) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0590 : CheckedFact 590 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 590) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_0591 : CheckedFact 591 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 591) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_0597 : CheckedFact 597 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 597) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0602 : CheckedFact 602 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 602) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0604 : CheckedFact 604 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 604) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0605 : CheckedFact 605 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 605) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0607 : CheckedFact 607 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 607) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0608 : CheckedFact 608 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 608) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0618 : CheckedFact 618 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 618) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0620 : CheckedFact 620 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 620) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0621 : CheckedFact 621 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 621) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_0622 : CheckedFact 622 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 622) (positions := (21,26))
      (by decide +kernel) T contained

theorem checked_0626 : CheckedFact 626 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 626) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0627 : CheckedFact 627 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 627) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0628 : CheckedFact 628 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 628) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0629 : CheckedFact 629 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 629) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0634 : CheckedFact 634 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 634) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0635 : CheckedFact 635 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 635) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0640 : CheckedFact 640 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 640) (positions := (21,27))
      (by decide +kernel) T contained

theorem checked_0641 : CheckedFact 641 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 641) (positions := (21,27))
      (by decide +kernel) T contained

theorem checked_0643 : CheckedFact 643 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 643) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0644 : CheckedFact 644 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 644) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0645 : CheckedFact 645 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 645) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0646 : CheckedFact 646 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 646) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0647 : CheckedFact 647 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 647) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0652 : CheckedFact 652 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 652) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0653 : CheckedFact 653 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 653) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0654 : CheckedFact 654 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 654) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0657 : CheckedFact 657 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 657) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0658 : CheckedFact 658 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 658) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0659 : CheckedFact 659 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 659) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0660 : CheckedFact 660 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 660) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0668 : CheckedFact 668 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 668) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0669 : CheckedFact 669 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 669) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0670 : CheckedFact 670 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 670) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0671 : CheckedFact 671 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 671) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0673 : CheckedFact 673 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 673) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0674 : CheckedFact 674 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 674) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0675 : CheckedFact 675 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 675) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0676 : CheckedFact 676 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 676) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0678 : CheckedFact 678 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 678) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0679 : CheckedFact 679 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 679) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0680 : CheckedFact 680 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 680) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0681 : CheckedFact 681 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 681) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0686 : CheckedFact 686 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 686) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0687 : CheckedFact 687 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 687) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0688 : CheckedFact 688 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 688) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0692 : CheckedFact 692 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 692) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0695 : CheckedFact 695 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 695) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0699 : CheckedFact 699 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 699) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0703 : CheckedFact 703 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 703) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0704 : CheckedFact 704 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 704) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0705 : CheckedFact 705 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 705) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0706 : CheckedFact 706 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 706) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0708 : CheckedFact 708 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 708) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0709 : CheckedFact 709 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 709) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0710 : CheckedFact 710 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 710) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0711 : CheckedFact 711 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 711) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0712 : CheckedFact 712 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 712) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0716 : CheckedFact 716 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 716) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0722 : CheckedFact 722 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 722) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0723 : CheckedFact 723 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 723) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0724 : CheckedFact 724 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 724) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0726 : CheckedFact 726 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 726) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0727 : CheckedFact 727 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 727) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0728 : CheckedFact 728 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 728) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0729 : CheckedFact 729 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 729) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0732 : CheckedFact 732 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 732) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0737 : CheckedFact 737 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 737) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0738 : CheckedFact 738 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 738) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0739 : CheckedFact 739 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 739) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0740 : CheckedFact 740 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 740) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0749 : CheckedFact 749 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 749) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0773 : CheckedFact 773 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 773)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 4 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0788 : CheckedFact 788 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 788) (positions := (25,26))
      (by decide +kernel) T contained

theorem checked_0793 : CheckedFact 793 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 793) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0794 : CheckedFact 794 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 794) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0795 : CheckedFact 795 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 795) (positions := (0,6))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7500_7700.Arithmetic.Run0004
