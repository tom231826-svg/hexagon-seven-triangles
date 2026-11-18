import HexagonCover.NBand.M8500_8700.Semantics
import HexagonCover.NISubsetData.Batch0007
import HexagonCover.NISubsetData.Batch0008
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.Arithmetic.Run0004
open Common Semantics DistanceLeaf

theorem checked_0463 : CheckedFact 463 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 463) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0465 : CheckedFact 465 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 465) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0467 : CheckedFact 467 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 467) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0468 : CheckedFact 468 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 468)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 4 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0469 : CheckedFact 469 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 469) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0470 : CheckedFact 470 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 470) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0473 : CheckedFact 473 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 473) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0477 : CheckedFact 477 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 477) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0482 : CheckedFact 482 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 482) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0483 : CheckedFact 483 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 483) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0484 : CheckedFact 484 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 484) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0487 : CheckedFact 487 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 487) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0488 : CheckedFact 488 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 488) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0490 : CheckedFact 490 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 490) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0491 : CheckedFact 491 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 491) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0492 : CheckedFact 492 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 492) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0494 : CheckedFact 494 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 494) (positions := (0,9))
      (by decide +kernel) T contained

theorem checked_0496 : CheckedFact 496 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 496) (positions := (0,9))
      (by decide +kernel) T contained

theorem checked_0497 : CheckedFact 497 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 497) (positions := (2,9))
      (by decide +kernel) T contained

theorem checked_0501 : CheckedFact 501 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 501) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0502 : CheckedFact 502 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 502) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0504 : CheckedFact 504 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 504) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0505 : CheckedFact 505 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 505) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0506 : CheckedFact 506 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 506) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0507 : CheckedFact 507 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 507) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0509 : CheckedFact 509 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 509) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0510 : CheckedFact 510 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 510) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0512 : CheckedFact 512 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 512) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0513 : CheckedFact 513 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 513) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0516 : CheckedFact 516 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 516) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0517 : CheckedFact 517 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0007.c0007_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0518 : CheckedFact 518 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 518) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0521 : CheckedFact 521 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 521)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 4 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0523 : CheckedFact 523 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 523) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0526 : CheckedFact 526 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 526) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0527 : CheckedFact 527 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 527) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0530 : CheckedFact 530 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 530) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0531 : CheckedFact 531 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 531) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0536 : CheckedFact 536 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 536) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0538 : CheckedFact 538 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 538) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0539 : CheckedFact 539 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 539) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0540 : CheckedFact 540 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 540) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0541 : CheckedFact 541 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 541) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0548 : CheckedFact 548 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 548) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0549 : CheckedFact 549 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 549) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0550 : CheckedFact 550 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0008.c0000_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0551 : CheckedFact 551 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 551) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0552 : CheckedFact 552 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 552) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0555 : CheckedFact 555 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 555) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0558 : CheckedFact 558 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 558) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0559 : CheckedFact 559 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 559) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0560 : CheckedFact 560 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 560) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0562 : CheckedFact 562 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 562)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 7 8) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0566 : CheckedFact 566 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 566) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0568 : CheckedFact 568 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 568) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0569 : CheckedFact 569 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 569) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0572 : CheckedFact 572 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 572) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0573 : CheckedFact 573 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 573) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0574 : CheckedFact 574 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0008.c0001_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0575 : CheckedFact 575 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 575) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0576 : CheckedFact 576 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 576) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0580 : CheckedFact 580 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 580) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0581 : CheckedFact 581 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 581) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0584 : CheckedFact 584 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 584) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0585 : CheckedFact 585 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 585) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0592 : CheckedFact 592 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 592) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0593 : CheckedFact 593 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 593) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0594 : CheckedFact 594 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 594) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0598 : CheckedFact 598 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 598) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0599 : CheckedFact 599 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 599) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0600 : CheckedFact 600 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 600) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0604 : CheckedFact 604 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 604) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0605 : CheckedFact 605 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 605) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0606 : CheckedFact 606 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 606) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0610 : CheckedFact 610 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 610) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0613 : CheckedFact 613 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 613) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0614 : CheckedFact 614 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 614) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0620 : CheckedFact 620 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 620) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0621 : CheckedFact 621 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 621) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0622 : CheckedFact 622 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 622) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0626 : CheckedFact 626 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 626) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0627 : CheckedFact 627 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 627) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0628 : CheckedFact 628 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 628) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0632 : CheckedFact 632 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 632) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0633 : CheckedFact 633 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 633) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0634 : CheckedFact 634 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 634) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0638 : CheckedFact 638 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 638) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0639 : CheckedFact 639 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 639) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0641 : CheckedFact 641 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 641) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0648 : CheckedFact 648 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 648) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0649 : CheckedFact 649 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 649) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0650 : CheckedFact 650 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 650) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0654 : CheckedFact 654 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 654) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0655 : CheckedFact 655 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 655) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0656 : CheckedFact 656 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 656) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0660 : CheckedFact 660 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 660) (positions := (0,8))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8500_8700.Arithmetic.Run0004
