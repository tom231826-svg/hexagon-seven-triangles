import HexagonCover.NBand.M7500_7700.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.Arithmetic.Run0001
open Common Semantics DistanceLeaf

theorem checked_0116 : CheckedFact 116 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 116) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0118 : CheckedFact 118 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 118) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0122 : CheckedFact 122 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 122) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0123 : CheckedFact 123 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 123) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0124 : CheckedFact 124 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 124) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0125 : CheckedFact 125 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 125) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0126 : CheckedFact 126 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 126) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0127 : CheckedFact 127 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 127) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0128 : CheckedFact 128 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 128) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0130 : CheckedFact 130 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 130) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0131 : CheckedFact 131 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 131) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0133 : CheckedFact 133 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 133) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0134 : CheckedFact 134 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 134) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0135 : CheckedFact 135 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 135) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0136 : CheckedFact 136 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 136) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0137 : CheckedFact 137 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 137) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0141 : CheckedFact 141 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 141) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0144 : CheckedFact 144 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 144) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0145 : CheckedFact 145 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 145) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0146 : CheckedFact 146 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 146) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0147 : CheckedFact 147 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 147) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0148 : CheckedFact 148 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 148) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0149 : CheckedFact 149 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 149) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0150 : CheckedFact 150 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 150) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0151 : CheckedFact 151 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 151) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0152 : CheckedFact 152 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 152)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0154 : CheckedFact 154 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 154) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0155 : CheckedFact 155 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 155) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0156 : CheckedFact 156 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 156) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0159 : CheckedFact 159 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 159) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0162 : CheckedFact 162 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 162) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0163 : CheckedFact 163 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 163) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0164 : CheckedFact 164 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 164) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0165 : CheckedFact 165 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 165) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0166 : CheckedFact 166 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 166) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0167 : CheckedFact 167 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 167) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0168 : CheckedFact 168 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 168) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0169 : CheckedFact 169 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 169) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0170 : CheckedFact 170 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 170) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0171 : CheckedFact 171 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 171) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0173 : CheckedFact 173 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 173) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0174 : CheckedFact 174 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 174) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0175 : CheckedFact 175 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 175) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0176 : CheckedFact 176 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 176) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0177 : CheckedFact 177 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 177)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0178 : CheckedFact 178 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 178) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0183 : CheckedFact 183 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 183) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0184 : CheckedFact 184 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 184) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0185 : CheckedFact 185 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 185) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0186 : CheckedFact 186 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 186) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0188 : CheckedFact 188 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 188) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0189 : CheckedFact 189 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 189) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0190 : CheckedFact 190 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 190) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0191 : CheckedFact 191 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 191) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0193 : CheckedFact 193 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 193) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0194 : CheckedFact 194 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 194) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0195 : CheckedFact 195 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 195) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0196 : CheckedFact 196 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 196) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0198 : CheckedFact 198 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 198)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0203 : CheckedFact 203 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 203) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0204 : CheckedFact 204 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 204) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0205 : CheckedFact 205 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 205) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0207 : CheckedFact 207 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 207) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0208 : CheckedFact 208 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 208) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0209 : CheckedFact 209 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 209) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0210 : CheckedFact 210 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 210) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0214 : CheckedFact 214 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 214) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0215 : CheckedFact 215 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 215) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0216 : CheckedFact 216 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 216) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0217 : CheckedFact 217 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 217) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0219 : CheckedFact 219 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 219)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0222 : CheckedFact 222 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 222) (positions := (0,3))
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

theorem checked_0227 : CheckedFact 227 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 227) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 231) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0234 : CheckedFact 234 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 234) (positions := (2,3))
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
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 237) (positions := (0,3))
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
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 242) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0243 : CheckedFact 243 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 243) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0246 : CheckedFact 246 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 246) (positions := (2,3))
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

end HexagonCover.NBand.M7500_7700.Arithmetic.Run0001
