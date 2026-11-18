import HexagonCover.NBand.M6900_7100.Semantics
import HexagonCover.NISubsetData.Batch0003
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.Arithmetic.Run0002
open Common Semantics DistanceLeaf

theorem checked_0260 : CheckedFact 260 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 260) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0262 : CheckedFact 262 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 262)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0264 : CheckedFact 264 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 264) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0265 : CheckedFact 265 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 265) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0266 : CheckedFact 266 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 266) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0267 : CheckedFact 267 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 267) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0269 : CheckedFact 269 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0003.c0005_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0270 : CheckedFact 270 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 270) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0271 : CheckedFact 271 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 271) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0272 : CheckedFact 272 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 272) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0274 : CheckedFact 274 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 274) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0275 : CheckedFact 275 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 275) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0276 : CheckedFact 276 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 276) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0277 : CheckedFact 277 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 277) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0279 : CheckedFact 279 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 279) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0281 : CheckedFact 281 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 281) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0282 : CheckedFact 282 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 282) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0283 : CheckedFact 283 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 283) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0285 : CheckedFact 285 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 285) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0287 : CheckedFact 287 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 287) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0288 : CheckedFact 288 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 288) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0289 : CheckedFact 289 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 289) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0291 : CheckedFact 291 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 291) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0293 : CheckedFact 293 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 293) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0294 : CheckedFact 294 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 294) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0297 : CheckedFact 297 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 297) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0301 : CheckedFact 301 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 301) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0302 : CheckedFact 302 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 302) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0303 : CheckedFact 303 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 303) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0307 : CheckedFact 307 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 307) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0308 : CheckedFact 308 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 308) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0309 : CheckedFact 309 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 309) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0311 : CheckedFact 311 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 311) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0312 : CheckedFact 312 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 312) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0313 : CheckedFact 313 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 313) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0315 : CheckedFact 315 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 315) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0316 : CheckedFact 316 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 316) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0318 : CheckedFact 318 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 318) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0319 : CheckedFact 319 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 319) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0320 : CheckedFact 320 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 320) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0322 : CheckedFact 322 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 322) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0325 : CheckedFact 325 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 325) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0326 : CheckedFact 326 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 326) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0327 : CheckedFact 327 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 327) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0328 : CheckedFact 328 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 328) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0331 : CheckedFact 331 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 331) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0332 : CheckedFact 332 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 332) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0333 : CheckedFact 333 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 333) (positions := (0,3))
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

theorem checked_0343 : CheckedFact 343 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 343) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0344 : CheckedFact 344 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 344) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0345 : CheckedFact 345 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 345) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0347 : CheckedFact 347 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 347) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0348 : CheckedFact 348 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 348) (positions := (0,3))
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

theorem checked_0355 : CheckedFact 355 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 355) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0356 : CheckedFact 356 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 356) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0357 : CheckedFact 357 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 357) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0358 : CheckedFact 358 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 358) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0359 : CheckedFact 359 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 359) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0362 : CheckedFact 362 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 362) (positions := (4,6))
      (by decide +kernel) T contained

theorem checked_0363 : CheckedFact 363 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 363) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0364 : CheckedFact 364 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 364) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0366 : CheckedFact 366 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 366) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0367 : CheckedFact 367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 367) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0368 : CheckedFact 368 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 368) (positions := (4,5))
      (by decide +kernel) T contained

theorem checked_0369 : CheckedFact 369 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 369) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0371 : CheckedFact 371 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 371) (positions := (3,5))
      (by decide +kernel) T contained

theorem checked_0372 : CheckedFact 372 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 372) (positions := (5,6))
      (by decide +kernel) T contained

theorem checked_0377 : CheckedFact 377 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 377) (positions := (6,7))
      (by decide +kernel) T contained

theorem checked_0378 : CheckedFact 378 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 378) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0379 : CheckedFact 379 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 379) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0380 : CheckedFact 380 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 380) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0381 : CheckedFact 381 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 381) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0382 : CheckedFact 382 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 382) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0388 : CheckedFact 388 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 388) (positions := (24,27))
      (by decide +kernel) T contained

theorem checked_0391 : CheckedFact 391 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 391) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0394 : CheckedFact 394 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 394) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0395 : CheckedFact 395 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 395) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0400 : CheckedFact 400 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 400) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0401 : CheckedFact 401 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 401) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0402 : CheckedFact 402 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 402) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0403 : CheckedFact 403 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 403) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0409 : CheckedFact 409 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 409) (positions := (24,25))
      (by decide +kernel) T contained

theorem checked_0413 : CheckedFact 413 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 413) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0415 : CheckedFact 415 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 415) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0416 : CheckedFact 416 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 416) (positions := (0,3))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6900_7100.Arithmetic.Run0002
