import HexagonCover.NBand.M8300_8500.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.Arithmetic.Run0002
open Common Semantics DistanceLeaf

theorem checked_0211 : CheckedFact 211 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 211)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0212 : CheckedFact 212 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 212) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0213 : CheckedFact 213 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 213) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0214 : CheckedFact 214 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 214) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0215 : CheckedFact 215 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 215) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0217 : CheckedFact 217 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 217)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0218 : CheckedFact 218 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 218) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0219 : CheckedFact 219 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 219) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0220 : CheckedFact 220 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 220) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0221 : CheckedFact 221 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 221) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0222 : CheckedFact 222 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 222) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0223 : CheckedFact 223 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 223) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0224 : CheckedFact 224 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 224) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0225 : CheckedFact 225 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 225) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0226 : CheckedFact 226 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 226) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0228 : CheckedFact 228 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 228) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0229 : CheckedFact 229 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 229) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0230 : CheckedFact 230 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 230) (positions := (0,3))
      (by decide +kernel) T contained

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

theorem checked_0237 : CheckedFact 237 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 237)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

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

theorem checked_0242 : CheckedFact 242 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 242)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0243 : CheckedFact 243 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 243) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0244 : CheckedFact 244 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 244) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0245 : CheckedFact 245 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 245) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0246 : CheckedFact 246 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 246) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0247 : CheckedFact 247 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 247) (positions := (0,3))
      (by decide +kernel) T contained

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

theorem checked_0252 : CheckedFact 252 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 252) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0253 : CheckedFact 253 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 253) (positions := (0,3))
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
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 256)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0257 : CheckedFact 257 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 257) (positions := (3,4))
      (by decide +kernel) T contained

theorem checked_0258 : CheckedFact 258 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 258) (positions := (0,3))
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

theorem checked_0265 : CheckedFact 265 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 265) (positions := (0,3))
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

theorem checked_0270 : CheckedFact 270 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 270) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0271 : CheckedFact 271 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 271)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0272 : CheckedFact 272 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 272) (positions := (2,3))
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

theorem checked_0276 : CheckedFact 276 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 276) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0277 : CheckedFact 277 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 277) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0278 : CheckedFact 278 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 278) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 281) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0282 : CheckedFact 282 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 282) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0283 : CheckedFact 283 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 283) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0284 : CheckedFact 284 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 284) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0285 : CheckedFact 285 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 285) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0286 : CheckedFact 286 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 286)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0287 : CheckedFact 287 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 287) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0288 : CheckedFact 288 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 288) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0289 : CheckedFact 289 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 289) (positions := (0,3))
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

theorem checked_0294 : CheckedFact 294 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 294) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0295 : CheckedFact 295 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 295) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0296 : CheckedFact 296 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 296) (positions := (0,3))
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
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 300)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0301 : CheckedFact 301 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 301) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0302 : CheckedFact 302 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 302) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0303 : CheckedFact 303 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 303) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0304 : CheckedFact 304 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 304) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0306 : CheckedFact 306 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 306) (positions := (0,3))
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

end HexagonCover.NBand.M8300_8500.Arithmetic.Run0002
