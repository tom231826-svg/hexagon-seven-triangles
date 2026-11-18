import HexagonCover.NBand.M8300_8500.Semantics
import HexagonCover.NISubsetData.Batch0007
import HexagonCover.PointSegmentLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.Arithmetic.Run0007
open Common Semantics DistanceLeaf

theorem checked_1163 : CheckedFact 1163 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1163) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1164 : CheckedFact 1164 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1164) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1165 : CheckedFact 1165 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1165) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1166 : CheckedFact 1166 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1166) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1168 : CheckedFact 1168 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1168) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1169 : CheckedFact 1169 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1169) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1170 : CheckedFact 1170 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1170)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1171 : CheckedFact 1171 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1171) (positions := (2,8))
      (by decide +kernel) T contained

theorem checked_1172 : CheckedFact 1172 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1172) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1173 : CheckedFact 1173 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1173) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1174 : CheckedFact 1174 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1174) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1176 : CheckedFact 1176 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1176)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1178 : CheckedFact 1178 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1178) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1181 : CheckedFact 1181 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1181)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1182 : CheckedFact 1182 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1182) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1187 : CheckedFact 1187 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1187) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1188 : CheckedFact 1188 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1188) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1189 : CheckedFact 1189 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1189) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1190 : CheckedFact 1190 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1190)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1191 : CheckedFact 1191 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1191) (positions := (2,7))
      (by decide +kernel) T contained

theorem checked_1192 : CheckedFact 1192 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1192) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1193 : CheckedFact 1193 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1193) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1194 : CheckedFact 1194 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1194) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1196 : CheckedFact 1196 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1196)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 5) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1200 : CheckedFact 1200 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1200) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1201 : CheckedFact 1201 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1201) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1202 : CheckedFact 1202 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1202)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1203 : CheckedFact 1203 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1203) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1205 : CheckedFact 1205 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1205)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 7) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1208 : CheckedFact 1208 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1208)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1210 : CheckedFact 1210 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1210) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1211 : CheckedFact 1211 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1211) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1212 : CheckedFact 1212 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1212) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1213 : CheckedFact 1213 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1213) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1217 : CheckedFact 1217 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1217) (positions := (2,6))
      (by decide +kernel) T contained

theorem checked_1218 : CheckedFact 1218 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1218)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 4) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1222 : CheckedFact 1222 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0007.c0002_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_1228 : CheckedFact 1228 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1228) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1229 : CheckedFact 1229 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1229) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1232 : CheckedFact 1232 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1232)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1238 : CheckedFact 1238 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1238)
      (r := Quadratic3.ofRat radiusSquared) (w := .point 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1239 : CheckedFact 1239 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1239) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1240 : CheckedFact 1240 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1240) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_1241 : CheckedFact 1241 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1241)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 2 3) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1242 : CheckedFact 1242 where
  excluded T contained hNI := by
    apply HexagonCover.NISubsetData.Batch0007.c0003_excluded T
    · exact contained
    · exact hNI (by decide +kernel)

theorem checked_1246 : CheckedFact 1246 where
  excluded T contained hNI := by
    have h := PointSegmentLeaf.cannot_be_nonintruding (points := obligations 1246)
      (r := Quadratic3.ofRat radiusSquared) (w := .segment 3 6) (by decide +kernel) T contained
    apply h
    simpa only [PointSegmentLeaf.NonIntruding, Semantics.NonIntrusion, Quadratic3.real_ofRat] using hNI (by decide +kernel)

theorem checked_1253 : CheckedFact 1253 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1253) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_1254 : CheckedFact 1254 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1254) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1255 : CheckedFact 1255 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1255) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_1274 : CheckedFact 1274 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1274) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1277 : CheckedFact 1277 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1277) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1283 : CheckedFact 1283 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1283) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1285 : CheckedFact 1285 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1285) (positions := (22,23))
      (by decide +kernel) T contained

theorem checked_1288 : CheckedFact 1288 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1288) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1312 : CheckedFact 1312 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1312) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1313 : CheckedFact 1313 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1313) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1314 : CheckedFact 1314 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1314) (positions := (2,4))
      (by decide +kernel) T contained

theorem checked_1315 : CheckedFact 1315 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1315) (positions := (0,7))
      (by decide +kernel) T contained

theorem checked_1316 : CheckedFact 1316 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1316) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1319 : CheckedFact 1319 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1319) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1320 : CheckedFact 1320 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1320) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1321 : CheckedFact 1321 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1321) (positions := (0,6))
      (by decide +kernel) T contained

theorem checked_1322 : CheckedFact 1322 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1322) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1323 : CheckedFact 1323 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1323) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1324 : CheckedFact 1324 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1324) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1325 : CheckedFact 1325 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1325) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_1326 : CheckedFact 1326 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1326) (positions := (23,25))
      (by decide +kernel) T contained

theorem checked_1327 : CheckedFact 1327 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1327) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1328 : CheckedFact 1328 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1328) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1330 : CheckedFact 1330 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1330) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1331 : CheckedFact 1331 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1331) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1332 : CheckedFact 1332 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1332) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1337 : CheckedFact 1337 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1337) (positions := (22,25))
      (by decide +kernel) T contained

theorem checked_1340 : CheckedFact 1340 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1340) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1341 : CheckedFact 1341 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1341) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1342 : CheckedFact 1342 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1342) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1343 : CheckedFact 1343 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1343) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1344 : CheckedFact 1344 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1344) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1345 : CheckedFact 1345 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1345) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1348 : CheckedFact 1348 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1348) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_1349 : CheckedFact 1349 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1349) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1350 : CheckedFact 1350 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1350) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1351 : CheckedFact 1351 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1351) (positions := (0,8))
      (by decide +kernel) T contained

theorem checked_1352 : CheckedFact 1352 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1352) (positions := (0,5))
      (by decide +kernel) T contained

theorem checked_1353 : CheckedFact 1353 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1353) (positions := (0,4))
      (by decide +kernel) T contained

theorem checked_1357 : CheckedFact 1357 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1357) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1359 : CheckedFact 1359 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1359) (positions := (21,23))
      (by decide +kernel) T contained

theorem checked_1361 : CheckedFact 1361 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1361) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1363 : CheckedFact 1363 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1363) (positions := (21,22))
      (by decide +kernel) T contained

theorem checked_1364 : CheckedFact 1364 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1364) (positions := (21,24))
      (by decide +kernel) T contained

theorem checked_1365 : CheckedFact 1365 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1365) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1366 : CheckedFact 1366 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1366) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1367 : CheckedFact 1367 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1367) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1368 : CheckedFact 1368 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1368) (positions := (0,3))
      (by decide +kernel) T contained

theorem checked_1369 : CheckedFact 1369 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1369) (positions := (2,3))
      (by decide +kernel) T contained

theorem checked_1370 : CheckedFact 1370 where
  excluded T contained _ :=
    DistanceLeaf.checkWitness_sound (points := obligations 1370) (positions := (21,24))
      (by decide +kernel) T contained

end HexagonCover.NBand.M8300_8500.Arithmetic.Run0007
