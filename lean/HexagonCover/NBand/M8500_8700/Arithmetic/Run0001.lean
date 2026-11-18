import HexagonCover.NBand.M8500_8700.Semantics
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.Arithmetic.Run0001
open Common Semantics DistanceLeaf

theorem checked_0107 : CheckedFact 107 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 107) (positions := (23,24))
      (by decide +kernel) T contained

theorem checked_0108 : CheckedFact 108 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 108) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0109 : CheckedFact 109 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 109) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0111 : CheckedFact 111 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 111) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0112 : CheckedFact 112 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 112) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0113 : CheckedFact 113 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 113) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_0114 : CheckedFact 114 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 114) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0115 : CheckedFact 115 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 115) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0117 : CheckedFact 117 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 117) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0118 : CheckedFact 118 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 118) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0119 : CheckedFact 119 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 119) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_0120 : CheckedFact 120 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 120) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 124) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0125 : CheckedFact 125 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 125) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_0127 : CheckedFact 127 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 127) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 130) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 135) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0136 : CheckedFact 136 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 136) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0137 : CheckedFact 137 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 137)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0138 : CheckedFact 138 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 138) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 142) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0143 : CheckedFact 143 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 143) (positions := (21,25))
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
    DistanceLeaf.checkWitness_sound (points := obligations 148) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0150 : CheckedFact 150 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 150) (positions := (2,3))
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

theorem checked_0155 : CheckedFact 155 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 155)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_0156 : CheckedFact 156 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 156) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0157 : CheckedFact 157 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 157) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0158 : CheckedFact 158 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 158) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0159 : CheckedFact 159 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 159) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0160 : CheckedFact 160 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 160) (positions := (0,3))
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
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 166) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0167 : CheckedFact 167 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 167) (positions := (21,25))
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

theorem checked_0172 : CheckedFact 172 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 172) (positions := (2,3))
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

theorem checked_0178 : CheckedFact 178 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 178) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0181 : CheckedFact 181 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 181) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0182 : CheckedFact 182 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 182) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0183 : CheckedFact 183 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 183) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0184 : CheckedFact 184 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 184) (positions := (0,3))
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
    DistanceLeaf.checkWitness_sound (points := obligations 189) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0190 : CheckedFact 190 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 190) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0192 : CheckedFact 192 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 192) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0194 : CheckedFact 194 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 194) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_0195 : CheckedFact 195 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 195) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0196 : CheckedFact 196 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 196) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0197 : CheckedFact 197 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 197) (positions := (21,24))
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

theorem checked_0201 : CheckedFact 201 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 201) (positions := (0,3))
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

theorem checked_0206 : CheckedFact 206 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 206) (positions := (21,22))
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

theorem checked_0214 : CheckedFact 214 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 214) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_0215 : CheckedFact 215 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 215) (positions := (21,22))
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

theorem checked_0221 : CheckedFact 221 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 221) (positions := (0,3))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8500_8700.Arithmetic.Run0001
