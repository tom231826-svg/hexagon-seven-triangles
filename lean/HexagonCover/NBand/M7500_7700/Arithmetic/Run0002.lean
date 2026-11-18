import HexagonCover.NBand.M7500_7700.Semantics
import HexagonCover.NISubsetData.Batch0006
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.Arithmetic.Run0002
open Common Semantics DistanceLeaf

theorem checked_0256 : CheckedFact 256 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 256) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0259 : CheckedFact 259 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 259) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0260 : CheckedFact 260 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 260) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0261 : CheckedFact 261 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 261) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0263 : CheckedFact 263 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 263) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0264 : CheckedFact 264 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 264) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_0266 : CheckedFact 266 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 266) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0267 : CheckedFact 267 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 267) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0268 : CheckedFact 268 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 268) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0269 : CheckedFact 269 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 269) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0272 : CheckedFact 272 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 272) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0273 : CheckedFact 273 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 273) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0274 : CheckedFact 274 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 274) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0275 : CheckedFact 275 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 275) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0277 : CheckedFact 277 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0006.c0002_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0280 : CheckedFact 280 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 280) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0281 : CheckedFact 281 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 281) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0282 : CheckedFact 282 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 282) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0284 : CheckedFact 284 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 284)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0286 : CheckedFact 286 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 286) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0287 : CheckedFact 287 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 287) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0288 : CheckedFact 288 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 288) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0290 : CheckedFact 290 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 290) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0291 : CheckedFact 291 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 291) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0292 : CheckedFact 292 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 292) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0293 : CheckedFact 293 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 293) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0295 : CheckedFact 295 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 295) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0296 : CheckedFact 296 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 296) (positions := (22,23))
      (by decide +kernel) T contained

theorem checked_0297 : CheckedFact 297 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 297) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0298 : CheckedFact 298 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 298) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0299 : CheckedFact 299 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 299) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0301 : CheckedFact 301 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 301) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0303 : CheckedFact 303 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 303) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0304 : CheckedFact 304 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 304) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0305 : CheckedFact 305 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 305) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0307 : CheckedFact 307 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 307) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0309 : CheckedFact 309 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 309) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0310 : CheckedFact 310 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 310) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0313 : CheckedFact 313 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 313) (positions := (0,3))
      (by decide +kernel) T contained

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

theorem checked_0320 : CheckedFact 320 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 320) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0325 : CheckedFact 325 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 325) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0327 : CheckedFact 327 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 327) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0328 : CheckedFact 328 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 328) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0329 : CheckedFact 329 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 329) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0332 : CheckedFact 332 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 332) (positions := (2,3))
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

theorem checked_0338 : CheckedFact 338 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 338) (positions := (2,3))
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

theorem checked_0344 : CheckedFact 344 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 344) (positions := (0,3))
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

theorem checked_0357 : CheckedFact 357 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 357) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0358 : CheckedFact 358 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 358) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0360 : CheckedFact 360 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 360) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0361 : CheckedFact 361 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 361) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0363 : CheckedFact 363 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 363) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0364 : CheckedFact 364 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 364) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0365 : CheckedFact 365 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 365) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0367 : CheckedFact 367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 367) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0369 : CheckedFact 369 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 369) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0370 : CheckedFact 370 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 370) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0372 : CheckedFact 372 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 372) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0373 : CheckedFact 373 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 373) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0375 : CheckedFact 375 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 375) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0377 : CheckedFact 377 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 377) (positions := (0,3))
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

theorem checked_0383 : CheckedFact 383 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 383) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0384 : CheckedFact 384 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 384) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0385 : CheckedFact 385 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 385) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0386 : CheckedFact 386 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 386) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0388 : CheckedFact 388 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 388) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0389 : CheckedFact 389 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 389) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0390 : CheckedFact 390 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 390) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0391 : CheckedFact 391 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 391) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0392 : CheckedFact 392 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 392) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0393 : CheckedFact 393 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 393) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0394 : CheckedFact 394 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 394) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0397 : CheckedFact 397 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 397) (positions := (0,6))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7500_7700.Arithmetic.Run0002
