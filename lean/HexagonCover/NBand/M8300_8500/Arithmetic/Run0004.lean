import HexagonCover.NBand.M8300_8500.Semantics
import HexagonCover.NISubsetData.Batch0006
import HexagonCover.NISubsetData.Batch0007
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.Arithmetic.Run0004
open Common Semantics DistanceLeaf

theorem checked_0475 : CheckedFact 475 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 475) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0478 : CheckedFact 478 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 478) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0479 : CheckedFact 479 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 479)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0481 : CheckedFact 481 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 481)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0485 : CheckedFact 485 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 485) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0486 : CheckedFact 486 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 486) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0487 : CheckedFact 487 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 487) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0488 : CheckedFact 488 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 488)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0492 : CheckedFact 492 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 492)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0493 : CheckedFact 493 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 493) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0496 : CheckedFact 496 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 496) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0498 : CheckedFact 498 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 498) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0500 : CheckedFact 500 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 500) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0501 : CheckedFact 501 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 501) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0502 : CheckedFact 502 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 502) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0503 : CheckedFact 503 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 503) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0508 : CheckedFact 508 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 508) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0509 : CheckedFact 509 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 509) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0510 : CheckedFact 510 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 510)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 8) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0511 : CheckedFact 511 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 511) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0513 : CheckedFact 513 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 513)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 8) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0515 : CheckedFact 515 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 515)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0520 : CheckedFact 520 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 520)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0522 : CheckedFact 522 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 522) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0525 : CheckedFact 525 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 525) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0527 : CheckedFact 527 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 527) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0528 : CheckedFact 528 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 528) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0533 : CheckedFact 533 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 533) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0534 : CheckedFact 534 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 534) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0535 : CheckedFact 535 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 535)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0536 : CheckedFact 536 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 536) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0538 : CheckedFact 538 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 538)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0539 : CheckedFact 539 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 539)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0540 : CheckedFact 540 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 540)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0541 : CheckedFact 541 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 541) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0542 : CheckedFact 542 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 542) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0545 : CheckedFact 545 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 545) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0546 : CheckedFact 546 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 546)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0548 : CheckedFact 548 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 548)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0549 : CheckedFact 549 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 549) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0550 : CheckedFact 550 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 550) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0555 : CheckedFact 555 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 555) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0556 : CheckedFact 556 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 556) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0557 : CheckedFact 557 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 557)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0558 : CheckedFact 558 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 558) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0560 : CheckedFact 560 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 560)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0561 : CheckedFact 561 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 561)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0562 : CheckedFact 562 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 562) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0563 : CheckedFact 563 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 563) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0565 : CheckedFact 565 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 565) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0572 : CheckedFact 572 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 572) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0574 : CheckedFact 574 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0006.c0007_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0579 : CheckedFact 579 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 579) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0580 : CheckedFact 580 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 580) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0581 : CheckedFact 581 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 581) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0586 : CheckedFact 586 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 586) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0589 : CheckedFact 589 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0006.c0008_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0595 : CheckedFact 595 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 595) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0602 : CheckedFact 602 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 602) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0603 : CheckedFact 603 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 603) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0604 : CheckedFact 604 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 604)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0605 : CheckedFact 605 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 605) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0607 : CheckedFact 607 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 607) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0608 : CheckedFact 608 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 608) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0609 : CheckedFact 609 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 609) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0612 : CheckedFact 612 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 612)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0614 : CheckedFact 614 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 614) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0617 : CheckedFact 617 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 617) (positions := (2,9))
      (by decide +kernel) T contained

theorem checked_0618 : CheckedFact 618 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 618)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 4 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0619 : CheckedFact 619 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 619) (positions := (0,9))
      (by decide +kernel) T contained

theorem checked_0620 : CheckedFact 620 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 620) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0625 : CheckedFact 625 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0007.c0000_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0626 : CheckedFact 626 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 626) (positions := (0,3))
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
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0007.c0001_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0638 : CheckedFact 638 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 638)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 4 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0643 : CheckedFact 643 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 643)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 4 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0647 : CheckedFact 647 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 647) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_0648 : CheckedFact 648 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 648) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (2,8))
      (by decide +kernel) T contained

theorem checked_0656 : CheckedFact 656 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 656) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0668 : CheckedFact 668 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 668) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0669 : CheckedFact 669 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 669) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0671 : CheckedFact 671 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 671) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0674 : CheckedFact 674 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 674) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0675 : CheckedFact 675 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 675) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0676 : CheckedFact 676 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 676) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0677 : CheckedFact 677 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 677) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0678 : CheckedFact 678 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 678) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0679 : CheckedFact 679 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 679) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0682 : CheckedFact 682 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 682) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0683 : CheckedFact 683 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 683) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0684 : CheckedFact 684 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 684) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0694 : CheckedFact 694 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 694) (positions := (0,7))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8300_8500.Arithmetic.Run0004
