import HexagonCover.NBand.M7700_7900.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.Arithmetic.Run0002
open Common Semantics DistanceLeaf

theorem checked_0241 : CheckedFact 241 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 241) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0242 : CheckedFact 242 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 242) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0243 : CheckedFact 243 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 243) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0244 : CheckedFact 244 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 244) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0246 : CheckedFact 246 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 246)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0248 : CheckedFact 248 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 248) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0249 : CheckedFact 249 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 249) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0250 : CheckedFact 250 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 250) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0251 : CheckedFact 251 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 251) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0254 : CheckedFact 254 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 254) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0255 : CheckedFact 255 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 255) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0256 : CheckedFact 256 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 256) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0257 : CheckedFact 257 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 257) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0261 : CheckedFact 261 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 261) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0262 : CheckedFact 262 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 262) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0263 : CheckedFact 263 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 263) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0264 : CheckedFact 264 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 264) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0266 : CheckedFact 266 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 266) (positions := (22,23))
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

theorem checked_0271 : CheckedFact 271 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 271) (positions := (2,3))
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
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 277) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0279 : CheckedFact 279 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 279) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0280 : CheckedFact 280 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 280) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0281 : CheckedFact 281 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 281) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0283 : CheckedFact 283 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 283) (positions := (0,3))
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
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 291)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0293 : CheckedFact 293 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 293) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0294 : CheckedFact 294 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 294) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0295 : CheckedFact 295 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 295) (positions := (0,3))
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

theorem checked_0300 : CheckedFact 300 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 300) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0302 : CheckedFact 302 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 302) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0303 : CheckedFact 303 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 303) (positions := (22,23))
      (by decide +kernel) T contained

theorem checked_0304 : CheckedFact 304 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 304) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0305 : CheckedFact 305 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 305) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0306 : CheckedFact 306 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 306) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0308 : CheckedFact 308 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 308) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0310 : CheckedFact 310 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 310) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0311 : CheckedFact 311 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 311) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0312 : CheckedFact 312 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 312) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0314 : CheckedFact 314 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 314) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0316 : CheckedFact 316 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 316) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0317 : CheckedFact 317 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 317) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0320 : CheckedFact 320 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 320) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0322 : CheckedFact 322 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 322) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0324 : CheckedFact 324 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 324) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0325 : CheckedFact 325 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 325) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0326 : CheckedFact 326 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 326) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0328 : CheckedFact 328 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 328) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0332 : CheckedFact 332 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 332) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0333 : CheckedFact 333 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 333) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0335 : CheckedFact 335 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 335) (positions := (2,3))
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

theorem checked_0341 : CheckedFact 341 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 341) (positions := (2,3))
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

theorem checked_0347 : CheckedFact 347 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 347) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0348 : CheckedFact 348 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 348) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0349 : CheckedFact 349 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 349) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0351 : CheckedFact 351 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 351) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0352 : CheckedFact 352 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 352) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0353 : CheckedFact 353 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 353) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0354 : CheckedFact 354 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 354) (positions := (0,3))
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

theorem checked_0366 : CheckedFact 366 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 366) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0367 : CheckedFact 367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 367) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0368 : CheckedFact 368 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 368) (positions := (0,3))
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

theorem checked_0376 : CheckedFact 376 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 376) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0378 : CheckedFact 378 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 378) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0380 : CheckedFact 380 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 380) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0381 : CheckedFact 381 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 381) (positions := (0,3))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7700_7900.Arithmetic.Run0002
