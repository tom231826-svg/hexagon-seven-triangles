import HexagonCover.NBand.M6667_6700.Semantics
import HexagonCover.NISubsetData.Batch0001
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.Arithmetic.Run0002
open Common Semantics DistanceLeaf

theorem checked_0231 : CheckedFact 231 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 231) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0233 : CheckedFact 233 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 233) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0234 : CheckedFact 234 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 234) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0235 : CheckedFact 235 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 235) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0236 : CheckedFact 236 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 236) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0238 : CheckedFact 238 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 238) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0239 : CheckedFact 239 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 239) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0240 : CheckedFact 240 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 240) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0241 : CheckedFact 241 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 241) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0243 : CheckedFact 243 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 243) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0244 : CheckedFact 244 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 244) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_0245 : CheckedFact 245 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 245) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0246 : CheckedFact 246 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 246) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0247 : CheckedFact 247 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 247) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0249 : CheckedFact 249 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0002_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0250 : CheckedFact 250 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 250) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0254 : CheckedFact 254 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 254) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0255 : CheckedFact 255 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 255) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0257 : CheckedFact 257 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 257) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0260 : CheckedFact 260 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 260) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0262 : CheckedFact 262 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 262) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0263 : CheckedFact 263 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 263) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0267 : CheckedFact 267 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 267) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0268 : CheckedFact 268 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 268) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0273 : CheckedFact 273 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0003_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0274 : CheckedFact 274 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 274) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0275 : CheckedFact 275 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 275) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0276 : CheckedFact 276 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 276) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0278 : CheckedFact 278 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 278) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0283 : CheckedFact 283 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0004_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0284 : CheckedFact 284 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 284) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0285 : CheckedFact 285 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 285) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0287 : CheckedFact 287 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 287) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0288 : CheckedFact 288 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 288) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0289 : CheckedFact 289 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 289) (positions := (26,27))
      (by decide +kernel) T contained

theorem checked_0294 : CheckedFact 294 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 294) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0298 : CheckedFact 298 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0005_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0300 : CheckedFact 300 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 300) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 307) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0309 : CheckedFact 309 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0006_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0311 : CheckedFact 311 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 311) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0312 : CheckedFact 312 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 312) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0313 : CheckedFact 313 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 313) (positions := (2,6))
      (by decide +kernel) T contained

theorem checked_0314 : CheckedFact 314 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0007_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0315 : CheckedFact 315 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 315) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0316 : CheckedFact 316 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 316) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0317 : CheckedFact 317 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 317) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0318 : CheckedFact 318 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 318) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0320 : CheckedFact 320 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0008_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0327 : CheckedFact 327 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 327) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_0328 : CheckedFact 328 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 328) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0329 : CheckedFact 329 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 329) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0330 : CheckedFact 330 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 330) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0332 : CheckedFact 332 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 332)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0334 : CheckedFact 334 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 334) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0337 : CheckedFact 337 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 337) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0338 : CheckedFact 338 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 338) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0341 : CheckedFact 341 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 341)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0344 : CheckedFact 344 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 344) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0345 : CheckedFact 345 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 345) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0347 : CheckedFact 347 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 347)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0349 : CheckedFact 349 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 349)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0353 : CheckedFact 353 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 353) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0355 : CheckedFact 355 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 355)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0357 : CheckedFact 357 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 357) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0358 : CheckedFact 358 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 358) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0361 : CheckedFact 361 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0001.c0009_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_0362 : CheckedFact 362 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 362) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0363 : CheckedFact 363 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 363) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0365 : CheckedFact 365 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 365)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0367 : CheckedFact 367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 367) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0368 : CheckedFact 368 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 368) (positions := (2,5))
      (by decide +kernel) T contained

theorem checked_0370 : CheckedFact 370 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 370) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0371 : CheckedFact 371 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 371)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0373 : CheckedFact 373 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 373) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_0378 : CheckedFact 378 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 378) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0379 : CheckedFact 379 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 379) (positions := (2,6))
      (by decide +kernel) T contained

theorem checked_0381 : CheckedFact 381 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 381) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0382 : CheckedFact 382 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 382) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0384 : CheckedFact 384 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 384) (positions := (2,5))
      (by decide +kernel) T contained

theorem checked_0385 : CheckedFact 385 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 385) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0387 : CheckedFact 387 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 387) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_0388 : CheckedFact 388 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 388) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_0389 : CheckedFact 389 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 389) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0390 : CheckedFact 390 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 390) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0391 : CheckedFact 391 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 391) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0392 : CheckedFact 392 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 392) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0393 : CheckedFact 393 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 393) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0394 : CheckedFact 394 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 394) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0396 : CheckedFact 396 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 396) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0397 : CheckedFact 397 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 397) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0398 : CheckedFact 398 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 398) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0399 : CheckedFact 399 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 399) (positions := (0,3))
      (by decide +kernel) T contained

end HexagonCover.NBand.M6667_6700.Arithmetic.Run0002
