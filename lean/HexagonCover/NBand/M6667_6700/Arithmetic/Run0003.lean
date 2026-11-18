import HexagonCover.NBand.M6667_6700.Semantics
import HexagonCover.NISubsetData.Batch0001
import HexagonCover.NISubsetData.Batch0002
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.Arithmetic.Run0003
open Common Semantics DistanceLeaf

theorem checked_0400 : CheckedFact 400 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 400) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0401 : CheckedFact 401 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 401) (positions := (25,26))
      (by decide +kernel) T contained

theorem checked_0402 : CheckedFact 402 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 402) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0403 : CheckedFact 403 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 403) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0404 : CheckedFact 404 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 404) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0406 : CheckedFact 406 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 406) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0408 : CheckedFact 408 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 408) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0409 : CheckedFact 409 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 409) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0410 : CheckedFact 410 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 410) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0411 : CheckedFact 411 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 411) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0412 : CheckedFact 412 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 412) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0414 : CheckedFact 414 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 414) (positions := (21,25))
      (by decide +kernel) T contained

theorem checked_0415 : CheckedFact 415 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 415) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0416 : CheckedFact 416 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 416) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0417 : CheckedFact 417 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 417) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0419 : CheckedFact 419 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 419) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0426 : CheckedFact 426 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 426) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0427 : CheckedFact 427 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 427) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0428 : CheckedFact 428 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 428) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0429 : CheckedFact 429 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 429) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0430 : CheckedFact 430 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 430)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0434 : CheckedFact 434 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 434) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0435 : CheckedFact 435 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 435) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0436 : CheckedFact 436 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 436) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0439 : CheckedFact 439 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 439) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0440 : CheckedFact 440 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 440) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0441 : CheckedFact 441 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 441) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0442 : CheckedFact 442 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 442) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0443 : CheckedFact 443 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 443) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0444 : CheckedFact 444 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 444)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0448 : CheckedFact 448 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 448) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0449 : CheckedFact 449 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 449) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0450 : CheckedFact 450 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 450) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0451 : CheckedFact 451 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 451) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0452 : CheckedFact 452 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 452)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0462 : CheckedFact 462 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 462) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0463 : CheckedFact 463 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 463) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0466 : CheckedFact 466 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 466) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0467 : CheckedFact 467 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 467) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0468 : CheckedFact 468 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 468) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0469 : CheckedFact 469 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 469) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0471 : CheckedFact 471 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 471) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0472 : CheckedFact 472 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 472) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0473 : CheckedFact 473 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 473) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0474 : CheckedFact 474 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 474) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0476 : CheckedFact 476 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 476) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0477 : CheckedFact 477 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 477) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0478 : CheckedFact 478 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 478) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0479 : CheckedFact 479 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 479) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0481 : CheckedFact 481 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 481) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0485 : CheckedFact 485 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 485) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0486 : CheckedFact 486 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 486) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0487 : CheckedFact 487 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 487) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0488 : CheckedFact 488 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 488) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0489 : CheckedFact 489 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 489)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0490 : CheckedFact 490 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 490) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0491 : CheckedFact 491 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 491) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0492 : CheckedFact 492 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 492) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0495 : CheckedFact 495 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 495) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0497 : CheckedFact 497 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 497) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0498 : CheckedFact 498 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 498) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0499 : CheckedFact 499 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 499) (positions := (0,5))
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
    DistanceLeaf.checkWitness_sound (points := obligations 510) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0513 : CheckedFact 513 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 513) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0514 : CheckedFact 514 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 514) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_0515 : CheckedFact 515 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 515) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0517 : CheckedFact 517 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 517) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0519 : CheckedFact 519 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 519) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0521 : CheckedFact 521 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 521) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0522 : CheckedFact 522 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 522) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0523 : CheckedFact 523 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 523) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0525 : CheckedFact 525 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 525)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0527 : CheckedFact 527 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 527) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0528 : CheckedFact 528 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 528) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0529 : CheckedFact 529 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 529) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0531 : CheckedFact 531 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 531)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0537 : CheckedFact 537 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 537) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0538 : CheckedFact 538 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 538) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0541 : CheckedFact 541 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 541) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0555 : CheckedFact 555 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 555) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0556 : CheckedFact 556 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 556) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0557 : CheckedFact 557 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 557) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0559 : CheckedFact 559 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 559) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0562 : CheckedFact 562 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 562) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0563 : CheckedFact 563 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 563) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0564 : CheckedFact 564 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0010_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0571 : CheckedFact 571 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0002.c0000_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0578 : CheckedFact 578 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 578) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0579 : CheckedFact 579 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 579) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0580 : CheckedFact 580 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 580) (positions := (0,7))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6667_6700.Arithmetic.Run0003
