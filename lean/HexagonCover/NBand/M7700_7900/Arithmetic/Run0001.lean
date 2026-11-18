import HexagonCover.NBand.M7700_7900.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.Arithmetic.Run0001
open Common Semantics DistanceLeaf

theorem checked_0113 : CheckedFact 113 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 113) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0114 : CheckedFact 114 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 114) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0115 : CheckedFact 115 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 115) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0116 : CheckedFact 116 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 116)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0118 : CheckedFact 118 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 118) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0119 : CheckedFact 119 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 119) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0120 : CheckedFact 120 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 120) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0123 : CheckedFact 123 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 123) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0124 : CheckedFact 124 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 124) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0125 : CheckedFact 125 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 125) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0126 : CheckedFact 126 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 126) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0128 : CheckedFact 128 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 128) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0129 : CheckedFact 129 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 129) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0130 : CheckedFact 130 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 130) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0131 : CheckedFact 131 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 131) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0132 : CheckedFact 132 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 132) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0136 : CheckedFact 136 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 136) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0139 : CheckedFact 139 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 139) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0140 : CheckedFact 140 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 140) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0141 : CheckedFact 141 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 141) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0142 : CheckedFact 142 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 142) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0143 : CheckedFact 143 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 143) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0144 : CheckedFact 144 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 144) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 148) (positions := (21,22))
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
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 152) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0153 : CheckedFact 153 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 153) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0154 : CheckedFact 154 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 154)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0155 : CheckedFact 155 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 155) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0156 : CheckedFact 156 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 156) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0157 : CheckedFact 157 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 157) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0159 : CheckedFact 159 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 159) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0160 : CheckedFact 160 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 160) (positions := (22,24))
      (by decide +kernel) T contained

theorem checked_0161 : CheckedFact 161 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 161) (positions := (2,3))
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

theorem checked_0166 : CheckedFact 166 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 166)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0168 : CheckedFact 168 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 168) (positions := (2,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 171) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0173 : CheckedFact 173 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 173) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0175 : CheckedFact 175 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 175) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0176 : CheckedFact 176 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 176) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0177 : CheckedFact 177 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 177) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0178 : CheckedFact 178 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 178) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0180 : CheckedFact 180 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 180) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0181 : CheckedFact 181 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 181) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0182 : CheckedFact 182 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 182) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0183 : CheckedFact 183 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 183) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0185 : CheckedFact 185 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 185) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0186 : CheckedFact 186 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 186) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0187 : CheckedFact 187 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 187) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0188 : CheckedFact 188 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 188) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0189 : CheckedFact 189 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 189) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0191 : CheckedFact 191 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 191) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0192 : CheckedFact 192 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 192) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0193 : CheckedFact 193 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 193) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0194 : CheckedFact 194 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 194) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0195 : CheckedFact 195 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 195) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0197 : CheckedFact 197 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 197) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0198 : CheckedFact 198 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 198) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0199 : CheckedFact 199 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 199) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0200 : CheckedFact 200 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 200) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0202 : CheckedFact 202 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 202) (positions := (0,3))
      (by decide +kernel) T contained

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
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 207)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0210 : CheckedFact 210 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 210) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0211 : CheckedFact 211 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 211) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0212 : CheckedFact 212 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 212) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0213 : CheckedFact 213 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 213) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0216 : CheckedFact 216 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 216) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0217 : CheckedFact 217 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 217) (positions := (0,3))
      (by decide +kernel) T contained

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
    DistanceLeaf.checkWitness_sound (points := obligations 220) (positions := (21,22))
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
    DistanceLeaf.checkWitness_sound (points := obligations 227) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0229 : CheckedFact 229 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 229) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0230 : CheckedFact 230 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 230) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0231 : CheckedFact 231 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 231) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0232 : CheckedFact 232 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 232) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0234 : CheckedFact 234 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 234)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0236 : CheckedFact 236 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 236) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0237 : CheckedFact 237 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 237) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0238 : CheckedFact 238 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 238) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0239 : CheckedFact 239 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 239) (positions := (0,3))
      (by decide +kernel) T contained

end HexagonCover.NBand.M7700_7900.Arithmetic.Run0001
