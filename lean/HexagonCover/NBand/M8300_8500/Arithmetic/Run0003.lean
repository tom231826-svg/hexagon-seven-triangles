import HexagonCover.NBand.M8300_8500.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.Arithmetic.Run0003
open Common Semantics DistanceLeaf

theorem checked_0316 : CheckedFact 316 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 316) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0317 : CheckedFact 317 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 317) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0318 : CheckedFact 318 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 318) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0319 : CheckedFact 319 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 319) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0321 : CheckedFact 321 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 321) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0322 : CheckedFact 322 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 322) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0323 : CheckedFact 323 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 323) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0325 : CheckedFact 325 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 325) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0326 : CheckedFact 326 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 326) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0327 : CheckedFact 327 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 327) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0329 : CheckedFact 329 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 329)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0330 : CheckedFact 330 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 330) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0331 : CheckedFact 331 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 331) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0334 : CheckedFact 334 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 334) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0335 : CheckedFact 335 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 335) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0336 : CheckedFact 336 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 336) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0337 : CheckedFact 337 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 337) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0338 : CheckedFact 338 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 338) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0339 : CheckedFact 339 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 339) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0340 : CheckedFact 340 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 340) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0341 : CheckedFact 341 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 341) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0342 : CheckedFact 342 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 342) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0343 : CheckedFact 343 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 343) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0345 : CheckedFact 345 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 345) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0346 : CheckedFact 346 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 346) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0348 : CheckedFact 348 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 348) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0349 : CheckedFact 349 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 349) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0350 : CheckedFact 350 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 350) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0351 : CheckedFact 351 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 351) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0353 : CheckedFact 353 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 353) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0354 : CheckedFact 354 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 354) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0355 : CheckedFact 355 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 355) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0356 : CheckedFact 356 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 356) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0358 : CheckedFact 358 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 358) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0360 : CheckedFact 360 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 360) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0361 : CheckedFact 361 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 361) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0362 : CheckedFact 362 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 362) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0363 : CheckedFact 363 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 363) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0364 : CheckedFact 364 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 364)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0365 : CheckedFact 365 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 365) (positions := (2,9))
      (by decide +kernel) T contained

theorem checked_0366 : CheckedFact 366 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 366) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0367 : CheckedFact 367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 367) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0368 : CheckedFact 368 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 368) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0370 : CheckedFact 370 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 370)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0371 : CheckedFact 371 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 371) (positions := (0,9))
      (by decide +kernel) T contained

theorem checked_0372 : CheckedFact 372 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 372) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0376 : CheckedFact 376 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 376) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0380 : CheckedFact 380 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 380) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0381 : CheckedFact 381 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 381) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0382 : CheckedFact 382 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 382) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0384 : CheckedFact 384 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 384) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0385 : CheckedFact 385 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 385) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0386 : CheckedFact 386 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 386) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0390 : CheckedFact 390 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 390) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0391 : CheckedFact 391 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 391) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0393 : CheckedFact 393 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 393) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0394 : CheckedFact 394 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 394) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0395 : CheckedFact 395 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 395) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0396 : CheckedFact 396 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 396) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0400 : CheckedFact 400 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 400) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0402 : CheckedFact 402 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 402) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0403 : CheckedFact 403 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 403) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0404 : CheckedFact 404 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 404) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0405 : CheckedFact 405 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 405) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0406 : CheckedFact 406 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 406) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0411 : CheckedFact 411 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 411) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0412 : CheckedFact 412 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 412) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0413 : CheckedFact 413 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 413) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_0414 : CheckedFact 414 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 414) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0422 : CheckedFact 422 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 422) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0424 : CheckedFact 424 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 424) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0425 : CheckedFact 425 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 425) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0426 : CheckedFact 426 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 426) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0427 : CheckedFact 427 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 427) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0433 : CheckedFact 433 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 433) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0435 : CheckedFact 435 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 435) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0436 : CheckedFact 436 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 436)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0438 : CheckedFact 438 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 438)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0440 : CheckedFact 440 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 440) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0441 : CheckedFact 441 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 441) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0442 : CheckedFact 442 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 442) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0443 : CheckedFact 443 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 443) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0444 : CheckedFact 444 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 444) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0446 : CheckedFact 446 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 446) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0450 : CheckedFact 450 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 450) (positions := (2,9))
      (by decide +kernel) T contained

theorem checked_0452 : CheckedFact 452 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 452) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0453 : CheckedFact 453 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 453) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0454 : CheckedFact 454 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 454) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0456 : CheckedFact 456 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 456) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0459 : CheckedFact 459 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 459) (positions := (0,9))
      (by decide +kernel) T contained

theorem checked_0463 : CheckedFact 463 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 463) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0464 : CheckedFact 464 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 464) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0466 : CheckedFact 466 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 466) (positions := (2,10))
      (by decide +kernel) T contained

theorem checked_0469 : CheckedFact 469 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 469) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0470 : CheckedFact 470 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 470) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0474 : CheckedFact 474 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 474) (positions := (0,10))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8300_8500.Arithmetic.Run0003
