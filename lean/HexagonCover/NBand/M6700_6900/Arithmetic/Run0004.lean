import HexagonCover.NBand.M6700_6900.Semantics
import HexagonCover.NISubsetData.Batch0002
import HexagonCover.NISubsetData.Batch0003
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.Arithmetic.Run0004
open Common Semantics DistanceLeaf

theorem checked_0545 : CheckedFact 545 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 545) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0547 : CheckedFact 547 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 547) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0548 : CheckedFact 548 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 548) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0551 : CheckedFact 551 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 551) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0552 : CheckedFact 552 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 552) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0554 : CheckedFact 554 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 554) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0555 : CheckedFact 555 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 555)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0556 : CheckedFact 556 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 556) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0557 : CheckedFact 557 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 557) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0559 : CheckedFact 559 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 559)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0560 : CheckedFact 560 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 560) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0561 : CheckedFact 561 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 561) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0564 : CheckedFact 564 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 564) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0566 : CheckedFact 566 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 566) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0569 : CheckedFact 569 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 569) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0570 : CheckedFact 570 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 570) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0574 : CheckedFact 574 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 574) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0575 : CheckedFact 575 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 575) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0578 : CheckedFact 578 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 578) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0579 : CheckedFact 579 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 579)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0580 : CheckedFact 580 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 580) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0581 : CheckedFact 581 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 581) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0583 : CheckedFact 583 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 583)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0586 : CheckedFact 586 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 586) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0590 : CheckedFact 590 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 590) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0594 : CheckedFact 594 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 594) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0595 : CheckedFact 595 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 595) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0596 : CheckedFact 596 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 596) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0597 : CheckedFact 597 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 597) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0599 : CheckedFact 599 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 599)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0601 : CheckedFact 601 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 601) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0602 : CheckedFact 602 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 602) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0603 : CheckedFact 603 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 603) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0604 : CheckedFact 604 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 604) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0610 : CheckedFact 610 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 610) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0611 : CheckedFact 611 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 611) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0613 : CheckedFact 613 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 613)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0616 : CheckedFact 616 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0002.c0008_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0619 : CheckedFact 619 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0003.c0000_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0621 : CheckedFact 621 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 621) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0627 : CheckedFact 627 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 627) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0629 : CheckedFact 629 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 629) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0632 : CheckedFact 632 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 632) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0633 : CheckedFact 633 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 633) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0640 : CheckedFact 640 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 640) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0644 : CheckedFact 644 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 644) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0645 : CheckedFact 645 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 645) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0648 : CheckedFact 648 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 648) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0649 : CheckedFact 649 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 649) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0652 : CheckedFact 652 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 652) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0653 : CheckedFact 653 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 653) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0656 : CheckedFact 656 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 656) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0657 : CheckedFact 657 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 657) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0658 : CheckedFact 658 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 658)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0670 : CheckedFact 670 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 670) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0675 : CheckedFact 675 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 675) (positions := (23,27))
      (by decide +kernel) T contained

theorem checked_0680 : CheckedFact 680 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 680) (positions := (24,26))
      (by decide +kernel) T contained

theorem checked_0681 : CheckedFact 681 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 681) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0687 : CheckedFact 687 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 687) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0688 : CheckedFact 688 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 688) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0689 : CheckedFact 689 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 689) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0690 : CheckedFact 690 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 690) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0693 : CheckedFact 693 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 693) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0694 : CheckedFact 694 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 694) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0695 : CheckedFact 695 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 695) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0697 : CheckedFact 697 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 697) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0698 : CheckedFact 698 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 698) (positions := (25,27))
      (by decide +kernel) T contained

theorem checked_0699 : CheckedFact 699 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 699) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0700 : CheckedFact 700 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 700) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0701 : CheckedFact 701 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 701) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0704 : CheckedFact 704 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 704) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0706 : CheckedFact 706 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 706) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0707 : CheckedFact 707 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 707) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0709 : CheckedFact 709 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 709) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0711 : CheckedFact 711 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 711) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0713 : CheckedFact 713 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 713) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0715 : CheckedFact 715 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 715) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0718 : CheckedFact 718 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 718) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0721 : CheckedFact 721 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 721) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0723 : CheckedFact 723 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 723) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0726 : CheckedFact 726 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 726) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0727 : CheckedFact 727 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 727) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0729 : CheckedFact 729 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 729) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0730 : CheckedFact 730 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 730) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0732 : CheckedFact 732 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 732) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0733 : CheckedFact 733 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 733) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0743 : CheckedFact 743 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 743) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0746 : CheckedFact 746 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 746) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0747 : CheckedFact 747 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 747) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0748 : CheckedFact 748 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 748) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0749 : CheckedFact 749 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 749) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0750 : CheckedFact 750 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 750)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0752 : CheckedFact 752 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 752) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0753 : CheckedFact 753 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 753) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0755 : CheckedFact 755 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 755) (positions := (0,4))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6700_6900.Arithmetic.Run0004
