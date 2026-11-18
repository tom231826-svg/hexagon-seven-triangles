import HexagonCover.NBand.M7700_7900.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.Arithmetic.Run0004
open Common Semantics DistanceLeaf

theorem checked_0531 : CheckedFact 531 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 531) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0532 : CheckedFact 532 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 532) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0533 : CheckedFact 533 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 533) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0534 : CheckedFact 534 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 534) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0536 : CheckedFact 536 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 536) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0537 : CheckedFact 537 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 537) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0538 : CheckedFact 538 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 538) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0543 : CheckedFact 543 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 543) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0544 : CheckedFact 544 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 544) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0547 : CheckedFact 547 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 547) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0549 : CheckedFact 549 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 549) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0550 : CheckedFact 550 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 550) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0551 : CheckedFact 551 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 551) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0552 : CheckedFact 552 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 552) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0563 : CheckedFact 563 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 563) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0564 : CheckedFact 564 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 564) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0565 : CheckedFact 565 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 565) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0566 : CheckedFact 566 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 566)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0567 : CheckedFact 567 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 567) (positions := (24,26))
      (by decide +kernel) T contained

theorem checked_0568 : CheckedFact 568 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 568) (positions := (3,6))
      (by decide +kernel) T contained

theorem checked_0569 : CheckedFact 569 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 569) (positions := (3,6))
      (by decide +kernel) T contained

theorem checked_0574 : CheckedFact 574 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 574) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0575 : CheckedFact 575 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 575) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0577 : CheckedFact 577 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 577) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_0578 : CheckedFact 578 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 578) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_0585 : CheckedFact 585 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 585) (positions := (25,26))
      (by decide +kernel) T contained

theorem checked_0593 : CheckedFact 593 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 593) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0595 : CheckedFact 595 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 595) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0596 : CheckedFact 596 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 596) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0597 : CheckedFact 597 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 597) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0598 : CheckedFact 598 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 598) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0599 : CheckedFact 599 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 599) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0606 : CheckedFact 606 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 606) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0607 : CheckedFact 607 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 607) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0608 : CheckedFact 608 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 608) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0609 : CheckedFact 609 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 609) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0612 : CheckedFact 612 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 612) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0626 : CheckedFact 626 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 626) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0635 : CheckedFact 635 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 635) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0636 : CheckedFact 636 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 636) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0641 : CheckedFact 641 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 641) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0642 : CheckedFact 642 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 642) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0643 : CheckedFact 643 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 643) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0644 : CheckedFact 644 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 644) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0645 : CheckedFact 645 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 645)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0656 : CheckedFact 656 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 656) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0657 : CheckedFact 657 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 657) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0658 : CheckedFact 658 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 658) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0659 : CheckedFact 659 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 659) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0660 : CheckedFact 660 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 660) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0664 : CheckedFact 664 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 664) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0665 : CheckedFact 665 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 665) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0672 : CheckedFact 672 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 672) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0673 : CheckedFact 673 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 673) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0674 : CheckedFact 674 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 674) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0686 : CheckedFact 686 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 686) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0687 : CheckedFact 687 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 687) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0688 : CheckedFact 688 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 688) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0690 : CheckedFact 690 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 690) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0693 : CheckedFact 693 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 693) (positions := (24,27))
      (by decide +kernel) T contained

theorem checked_0695 : CheckedFact 695 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 695) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0696 : CheckedFact 696 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 696) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0697 : CheckedFact 697 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 697) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0714 : CheckedFact 714 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 714) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0715 : CheckedFact 715 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 715) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0716 : CheckedFact 716 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 716) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0717 : CheckedFact 717 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 717) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0728 : CheckedFact 728 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 728) (positions := (2,6))
      (by decide +kernel) T contained

theorem checked_0729 : CheckedFact 729 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 729) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0730 : CheckedFact 730 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 730) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0731 : CheckedFact 731 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 731) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0734 : CheckedFact 734 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 734) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0735 : CheckedFact 735 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 735) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0738 : CheckedFact 738 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 738) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0740 : CheckedFact 740 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 740) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0742 : CheckedFact 742 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 742) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0745 : CheckedFact 745 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 745) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0769 : CheckedFact 769 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 769) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0770 : CheckedFact 770 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 770) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0771 : CheckedFact 771 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 771) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0793 : CheckedFact 793 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 793) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0794 : CheckedFact 794 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 794) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0798 : CheckedFact 798 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 798) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_0799 : CheckedFact 799 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 799) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0800 : CheckedFact 800 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 800) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0801 : CheckedFact 801 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 801) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0810 : CheckedFact 810 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 810) (positions := (25,26))
      (by decide +kernel) T contained

theorem checked_0819 : CheckedFact 819 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 819) (positions := (0,5))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7700_7900.Arithmetic.Run0004
