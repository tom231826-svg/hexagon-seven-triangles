import HexagonCover.PointSegmentLeaf
import HexagonCover.DistanceData.Common

/-! Actual original Q point/segment witnesses, emitted by an untrusted converter.
The previous numerical projection and gap claims are not used. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.PointSegmentData
open DistanceLeaf DistanceData.Coordinates

structure BoundWitness where
  family : DistanceData.Family
  factId : Nat
  role : Fin 7
  anchorId : Nat
  pointIds : List Nat
  points : List ExactPoint
  radiusSquared : ℚ
  witness : PointSegmentLeaf.Witness
  originalFlag : Bool
  sourceNI : Bool
  journalLine : Nat
  identity : String

structure CheckedWitness where
  data : BoundWitness
  checked : PointSegmentLeaf.check data.points (Quadratic3.ofRat data.radiusSquared) data.witness = true

theorem CheckedWitness.excluded (w : CheckedWitness) (T : UnitTriangle)
    (contained : ∀ p, p ∈ w.data.points → toPlane p ∈ T.region) :
    ¬ PointSegmentLeaf.NonIntruding T (Quadratic3.ofRat w.data.radiusSquared) :=
  PointSegmentLeaf.cannot_be_nonintruding w.checked T contained

def w0000 : CheckedWitness where
  data := {
    family := .q25
    factId := 174
    role := 2
    anchorId := 255
    pointIds := [255,47]
    points := [p0008,p0047]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 175
    identity := "5d0abc8154a4eab0f19b96192396ce618eef30bc3a805694391543da3154d44e" }
  checked := by decide +kernel

theorem w0000_check : PointSegmentLeaf.check w0000.data.points
    (Quadratic3.ofRat w0000.data.radiusSquared) w0000.data.witness = true := w0000.checked

def w0001 : CheckedWitness where
  data := {
    family := .q25
    factId := 178
    role := 2
    anchorId := 255
    pointIds := [255,48]
    points := [p0008,p0048]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 179
    identity := "ac260659bd2640bd8a5eaca647e7ce3d624917d4ad272dfe8033b70496a1c753" }
  checked := by decide +kernel

theorem w0001_check : PointSegmentLeaf.check w0001.data.points
    (Quadratic3.ofRat w0001.data.radiusSquared) w0001.data.witness = true := w0001.checked

def w0002 : CheckedWitness where
  data := {
    family := .q25
    factId := 182
    role := 2
    anchorId := 255
    pointIds := [255,49]
    points := [p0008,p0049]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 183
    identity := "850e36246a396500edc18d1a9064ccb27add09bb7d2575eebb939431d0b75e9b" }
  checked := by decide +kernel

theorem w0002_check : PointSegmentLeaf.check w0002.data.points
    (Quadratic3.ofRat w0002.data.radiusSquared) w0002.data.witness = true := w0002.checked

def w0003 : CheckedWitness where
  data := {
    family := .q25
    factId := 221
    role := 2
    anchorId := 255
    pointIds := [255,59]
    points := [p0008,p0059]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 222
    identity := "42a82a95b3206df1a6e5a5e857195aca3704cf595438627c8d7fba7ee45aaa55" }
  checked := by decide +kernel

theorem w0003_check : PointSegmentLeaf.check w0003.data.points
    (Quadratic3.ofRat w0003.data.radiusSquared) w0003.data.witness = true := w0003.checked

def w0004 : CheckedWitness where
  data := {
    family := .q25
    factId := 225
    role := 2
    anchorId := 255
    pointIds := [255,60]
    points := [p0008,p0060]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 226
    identity := "9d41eefe037e77c73231b63e3b1a383ca8a99fbd887738235b1247ff67d710c6" }
  checked := by decide +kernel

theorem w0004_check : PointSegmentLeaf.check w0004.data.points
    (Quadratic3.ofRat w0004.data.radiusSquared) w0004.data.witness = true := w0004.checked

def w0005 : CheckedWitness where
  data := {
    family := .q25
    factId := 229
    role := 2
    anchorId := 255
    pointIds := [255,61]
    points := [p0008,p0061]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 230
    identity := "3db820ae32023e980fc7ed5d32375da1ea7f2ab8d7309f74a9cbaddb12842829" }
  checked := by decide +kernel

theorem w0005_check : PointSegmentLeaf.check w0005.data.points
    (Quadratic3.ofRat w0005.data.radiusSquared) w0005.data.witness = true := w0005.checked

def w0006 : CheckedWitness where
  data := {
    family := .q25
    factId := 232
    role := 2
    anchorId := 255
    pointIds := [255,62]
    points := [p0008,p0062]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 233
    identity := "ade1643501eb66510787cff7c34668b2b27e4183ab867500f4d0f06ad0f4b169" }
  checked := by decide +kernel

theorem w0006_check : PointSegmentLeaf.check w0006.data.points
    (Quadratic3.ofRat w0006.data.radiusSquared) w0006.data.witness = true := w0006.checked

def w0007 : CheckedWitness where
  data := {
    family := .q25
    factId := 236
    role := 2
    anchorId := 255
    pointIds := [255,63]
    points := [p0008,p0063]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 237
    identity := "be04e3fd7b94eaae8bc689feb03eaf9718497092ce2f48a189129dbff294915e" }
  checked := by decide +kernel

theorem w0007_check : PointSegmentLeaf.check w0007.data.points
    (Quadratic3.ofRat w0007.data.radiusSquared) w0007.data.witness = true := w0007.checked

def w0008 : CheckedWitness where
  data := {
    family := .q25
    factId := 240
    role := 2
    anchorId := 255
    pointIds := [255,64]
    points := [p0008,p0064]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 241
    identity := "316d6a51852cdff5bf3c349d39c3a2a5d9ea75967413284fa91f9c2fd6bb70c7" }
  checked := by decide +kernel

theorem w0008_check : PointSegmentLeaf.check w0008.data.points
    (Quadratic3.ofRat w0008.data.radiusSquared) w0008.data.witness = true := w0008.checked

def w0009 : CheckedWitness where
  data := {
    family := .q25
    factId := 281
    role := 2
    anchorId := 255
    pointIds := [255,74]
    points := [p0008,p0074]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 282
    identity := "c2185844b317a93675efdf00a41bfcb2c16bda8b15d0149ffb7d317a3b01d85a" }
  checked := by decide +kernel

theorem w0009_check : PointSegmentLeaf.check w0009.data.points
    (Quadratic3.ofRat w0009.data.radiusSquared) w0009.data.witness = true := w0009.checked

def w0010 : CheckedWitness where
  data := {
    family := .q25
    factId := 285
    role := 2
    anchorId := 255
    pointIds := [255,75]
    points := [p0008,p0075]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 286
    identity := "d7026bf3b9fbd110c20d7af6f061107310305e54fb391845d0e8139da2c0c89e" }
  checked := by decide +kernel

theorem w0010_check : PointSegmentLeaf.check w0010.data.points
    (Quadratic3.ofRat w0010.data.radiusSquared) w0010.data.witness = true := w0010.checked

def w0011 : CheckedWitness where
  data := {
    family := .q25
    factId := 289
    role := 2
    anchorId := 255
    pointIds := [255,76]
    points := [p0008,p0076]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 290
    identity := "26d52baddbd2d426985153cd1a115841aa773a5c57eba37d72e49ddb41dabc91" }
  checked := by decide +kernel

theorem w0011_check : PointSegmentLeaf.check w0011.data.points
    (Quadratic3.ofRat w0011.data.radiusSquared) w0011.data.witness = true := w0011.checked

def w0012 : CheckedWitness where
  data := {
    family := .q25
    factId := 293
    role := 2
    anchorId := 255
    pointIds := [255,77]
    points := [p0008,p0077]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 294
    identity := "6f42514d59dc8920a16daccfb0c37c88d23be58b47555a341115963c07cf0d59" }
  checked := by decide +kernel

theorem w0012_check : PointSegmentLeaf.check w0012.data.points
    (Quadratic3.ofRat w0012.data.radiusSquared) w0012.data.witness = true := w0012.checked

def w0013 : CheckedWitness where
  data := {
    family := .q25
    factId := 297
    role := 2
    anchorId := 255
    pointIds := [255,78]
    points := [p0008,p0078]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 298
    identity := "8de2437ef5c947013676b627506ca1366998fb8bede925f7763b92b38a66d60c" }
  checked := by decide +kernel

theorem w0013_check : PointSegmentLeaf.check w0013.data.points
    (Quadratic3.ofRat w0013.data.radiusSquared) w0013.data.witness = true := w0013.checked

def w0014 : CheckedWitness where
  data := {
    family := .q25
    factId := 301
    role := 2
    anchorId := 255
    pointIds := [255,79]
    points := [p0008,p0079]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 302
    identity := "8a9bc1d4c93606448d32f300d4e1979860dd58369a295c2e94c8ba1bbafaa484" }
  checked := by decide +kernel

theorem w0014_check : PointSegmentLeaf.check w0014.data.points
    (Quadratic3.ofRat w0014.data.radiusSquared) w0014.data.witness = true := w0014.checked

def w0015 : CheckedWitness where
  data := {
    family := .q25
    factId := 338
    role := 5
    anchorId := 258
    pointIds := [258,88]
    points := [p0208,p0088]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 339
    identity := "f1bcf5d0c3b15a904659e53ffaa2bc2c8e3908c11c4c0a27fbb371195a35ba0f" }
  checked := by decide +kernel

theorem w0015_check : PointSegmentLeaf.check w0015.data.points
    (Quadratic3.ofRat w0015.data.radiusSquared) w0015.data.witness = true := w0015.checked

def w0016 : CheckedWitness where
  data := {
    family := .q25
    factId := 342
    role := 5
    anchorId := 258
    pointIds := [258,89]
    points := [p0208,p0089]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 343
    identity := "1caf3fd47013966fd207c7bb4e58e3904991efc2214fa5f872c347f6a2df0fa7" }
  checked := by decide +kernel

theorem w0016_check : PointSegmentLeaf.check w0016.data.points
    (Quadratic3.ofRat w0016.data.radiusSquared) w0016.data.witness = true := w0016.checked

def w0017 : CheckedWitness where
  data := {
    family := .q25
    factId := 349
    role := 2
    anchorId := 255
    pointIds := [255,91]
    points := [p0008,p0091]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 350
    identity := "d8a5f660391421e77ded6ab7f18491936cf1e3430d482bdb0a542bf2343b066c" }
  checked := by decide +kernel

theorem w0017_check : PointSegmentLeaf.check w0017.data.points
    (Quadratic3.ofRat w0017.data.radiusSquared) w0017.data.witness = true := w0017.checked

def w0018 : CheckedWitness where
  data := {
    family := .q25
    factId := 352
    role := 2
    anchorId := 255
    pointIds := [255,92]
    points := [p0008,p0092]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 353
    identity := "4932f0e813281e3faced38d0872430322983f9b6a63ddd547fd1c69a5d7fe770" }
  checked := by decide +kernel

theorem w0018_check : PointSegmentLeaf.check w0018.data.points
    (Quadratic3.ofRat w0018.data.radiusSquared) w0018.data.witness = true := w0018.checked

def w0019 : CheckedWitness where
  data := {
    family := .q25
    factId := 356
    role := 2
    anchorId := 255
    pointIds := [255,93]
    points := [p0008,p0093]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 357
    identity := "833582dea81a36cea0dcd815aa6fac01536d6229c7d5fdbaae3d4ac4b14113b8" }
  checked := by decide +kernel

theorem w0019_check : PointSegmentLeaf.check w0019.data.points
    (Quadratic3.ofRat w0019.data.radiusSquared) w0019.data.witness = true := w0019.checked

def w0020 : CheckedWitness where
  data := {
    family := .q25
    factId := 360
    role := 2
    anchorId := 255
    pointIds := [255,94]
    points := [p0008,p0094]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 361
    identity := "beaab010237d5a97c28697f47630872f05e4d274819df9b7db379773df2a8904" }
  checked := by decide +kernel

theorem w0020_check : PointSegmentLeaf.check w0020.data.points
    (Quadratic3.ofRat w0020.data.radiusSquared) w0020.data.witness = true := w0020.checked

def w0021 : CheckedWitness where
  data := {
    family := .q25
    factId := 364
    role := 2
    anchorId := 255
    pointIds := [255,95]
    points := [p0008,p0095]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 365
    identity := "517be1d6eeccec8e5c39a1519baa1dbec3240f5a387d9afbf81e05cd9a05fd75" }
  checked := by decide +kernel

theorem w0021_check : PointSegmentLeaf.check w0021.data.points
    (Quadratic3.ofRat w0021.data.radiusSquared) w0021.data.witness = true := w0021.checked

def w0022 : CheckedWitness where
  data := {
    family := .q25
    factId := 400
    role := 5
    anchorId := 258
    pointIds := [258,105]
    points := [p0208,p0105]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 401
    identity := "5b623ea8dc8cfe07803c188d7ea56a49b33607686598d01fba07177343f80a9a" }
  checked := by decide +kernel

theorem w0022_check : PointSegmentLeaf.check w0022.data.points
    (Quadratic3.ofRat w0022.data.radiusSquared) w0022.data.witness = true := w0022.checked

def w0023 : CheckedWitness where
  data := {
    family := .q25
    factId := 404
    role := 5
    anchorId := 258
    pointIds := [258,106]
    points := [p0208,p0106]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 405
    identity := "4fcc7843dd3845d07294f7babafcce1302362cf275db93dd130b85f4499f1e28" }
  checked := by decide +kernel

theorem w0023_check : PointSegmentLeaf.check w0023.data.points
    (Quadratic3.ofRat w0023.data.radiusSquared) w0023.data.witness = true := w0023.checked

def w0024 : CheckedWitness where
  data := {
    family := .q25
    factId := 408
    role := 5
    anchorId := 258
    pointIds := [258,107]
    points := [p0208,p0107]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 409
    identity := "c5934d718e4cd8d3122e086c4c4d455a61cf1cc4c9d6d5db3efb0da9ca82c690" }
  checked := by decide +kernel

theorem w0024_check : PointSegmentLeaf.check w0024.data.points
    (Quadratic3.ofRat w0024.data.radiusSquared) w0024.data.witness = true := w0024.checked

def w0025 : CheckedWitness where
  data := {
    family := .q25
    factId := 409
    role := 2
    anchorId := 255
    pointIds := [255,108]
    points := [p0008,p0108]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 410
    identity := "97e3423157937ea85bf92f79e5f20cb7c812490a091e181aa72f682727acb494" }
  checked := by decide +kernel

theorem w0025_check : PointSegmentLeaf.check w0025.data.points
    (Quadratic3.ofRat w0025.data.radiusSquared) w0025.data.witness = true := w0025.checked

def w0026 : CheckedWitness where
  data := {
    family := .q25
    factId := 410
    role := 5
    anchorId := 258
    pointIds := [258,108]
    points := [p0208,p0108]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 411
    identity := "f4c3790aaa30b704b9adcf5b5b55d600584e5754505016c2ebb86799f6494cb6" }
  checked := by decide +kernel

theorem w0026_check : PointSegmentLeaf.check w0026.data.points
    (Quadratic3.ofRat w0026.data.radiusSquared) w0026.data.witness = true := w0026.checked

def w0027 : CheckedWitness where
  data := {
    family := .q25
    factId := 411
    role := 2
    anchorId := 255
    pointIds := [255,109]
    points := [p0008,p0109]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 412
    identity := "22ad779b4517bda30bd4a1583fc407ae6840157b3aa2d3358193b074b8927e9f" }
  checked := by decide +kernel

theorem w0027_check : PointSegmentLeaf.check w0027.data.points
    (Quadratic3.ofRat w0027.data.radiusSquared) w0027.data.witness = true := w0027.checked

def w0028 : CheckedWitness where
  data := {
    family := .q25
    factId := 415
    role := 2
    anchorId := 255
    pointIds := [255,110]
    points := [p0008,p0110]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 416
    identity := "c46bc191fad043c0d82dba9dd4c638cb9a50ff3d935bbd7449637dcdfb1c6cf8" }
  checked := by decide +kernel

theorem w0028_check : PointSegmentLeaf.check w0028.data.points
    (Quadratic3.ofRat w0028.data.radiusSquared) w0028.data.witness = true := w0028.checked

def w0029 : CheckedWitness where
  data := {
    family := .q25
    factId := 419
    role := 2
    anchorId := 255
    pointIds := [255,111]
    points := [p0008,p0111]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 420
    identity := "a2803e8d8418e82a0c3942a0d8127ca3dcd13461042cae2355dc7ec20ef44b40" }
  checked := by decide +kernel

theorem w0029_check : PointSegmentLeaf.check w0029.data.points
    (Quadratic3.ofRat w0029.data.radiusSquared) w0029.data.witness = true := w0029.checked

def w0030 : CheckedWitness where
  data := {
    family := .q25
    factId := 455
    role := 5
    anchorId := 258
    pointIds := [258,121]
    points := [p0208,p0121]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 456
    identity := "d6b176fb2645b8f4fce481709988dd11b9d1035d2beae45c76bace85989e55e5" }
  checked := by decide +kernel

theorem w0030_check : PointSegmentLeaf.check w0030.data.points
    (Quadratic3.ofRat w0030.data.radiusSquared) w0030.data.witness = true := w0030.checked

def w0031 : CheckedWitness where
  data := {
    family := .q25
    factId := 459
    role := 5
    anchorId := 258
    pointIds := [258,122]
    points := [p0208,p0122]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 460
    identity := "d3bd8564e9bcbc086c2f9fcf8037c25d343462ebe98785abd6e73f7c9dc4e9ee" }
  checked := by decide +kernel

theorem w0031_check : PointSegmentLeaf.check w0031.data.points
    (Quadratic3.ofRat w0031.data.radiusSquared) w0031.data.witness = true := w0031.checked

def w0032 : CheckedWitness where
  data := {
    family := .q25
    factId := 464
    role := 5
    anchorId := 258
    pointIds := [258,123]
    points := [p0208,p0123]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 465
    identity := "7b3fb0d428746441ae2bea50e41cd88956c73bff70a12eb486da0a1dda3442a9" }
  checked := by decide +kernel

theorem w0032_check : PointSegmentLeaf.check w0032.data.points
    (Quadratic3.ofRat w0032.data.radiusSquared) w0032.data.witness = true := w0032.checked

def w0033 : CheckedWitness where
  data := {
    family := .q25
    factId := 468
    role := 5
    anchorId := 258
    pointIds := [258,124]
    points := [p0208,p0124]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 469
    identity := "4ad19d2668b5d9b73391845cfd230f5a839b12c915b77950bcd51bee0d3f5b7e" }
  checked := by decide +kernel

theorem w0033_check : PointSegmentLeaf.check w0033.data.points
    (Quadratic3.ofRat w0033.data.radiusSquared) w0033.data.witness = true := w0033.checked

def w0034 : CheckedWitness where
  data := {
    family := .q25
    factId := 472
    role := 5
    anchorId := 258
    pointIds := [258,125]
    points := [p0208,p0125]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 473
    identity := "f89452b1d02470e5afd4bc6aaeb84a8c5d1428e951ad1305032e793f76f7a7a9" }
  checked := by decide +kernel

theorem w0034_check : PointSegmentLeaf.check w0034.data.points
    (Quadratic3.ofRat w0034.data.radiusSquared) w0034.data.witness = true := w0034.checked

def w0035 : CheckedWitness where
  data := {
    family := .q25
    factId := 477
    role := 2
    anchorId := 255
    pointIds := [255,127]
    points := [p0008,p0127]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 478
    identity := "0abefbb6b5a6cee6b1903c8f9998e0e82dee5b7a49f6f6ef9dabeb69a56b68eb" }
  checked := by decide +kernel

theorem w0035_check : PointSegmentLeaf.check w0035.data.points
    (Quadratic3.ofRat w0035.data.radiusSquared) w0035.data.witness = true := w0035.checked

def w0036 : CheckedWitness where
  data := {
    family := .q25
    factId := 481
    role := 2
    anchorId := 255
    pointIds := [255,128]
    points := [p0008,p0128]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 482
    identity := "9f6cd0795a7803374dc4c1463abb6f5e9862309b6c03e09b45b322fb2f6db0de" }
  checked := by decide +kernel

theorem w0036_check : PointSegmentLeaf.check w0036.data.points
    (Quadratic3.ofRat w0036.data.radiusSquared) w0036.data.witness = true := w0036.checked

def w0037 : CheckedWitness where
  data := {
    family := .q25
    factId := 519
    role := 5
    anchorId := 258
    pointIds := [258,137]
    points := [p0208,p0137]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 520
    identity := "0d957ea6ca36ec94523a685f7c89e03bb39c238cfc99649403ffdee7c103a9d5" }
  checked := by decide +kernel

theorem w0037_check : PointSegmentLeaf.check w0037.data.points
    (Quadratic3.ofRat w0037.data.radiusSquared) w0037.data.witness = true := w0037.checked

def w0038 : CheckedWitness where
  data := {
    family := .q25
    factId := 523
    role := 5
    anchorId := 258
    pointIds := [258,138]
    points := [p0208,p0138]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 524
    identity := "7f6540c34a56e45a128df73212d934bf077d4357327fdf3c9f8feb72071ea753" }
  checked := by decide +kernel

theorem w0038_check : PointSegmentLeaf.check w0038.data.points
    (Quadratic3.ofRat w0038.data.radiusSquared) w0038.data.witness = true := w0038.checked

def w0039 : CheckedWitness where
  data := {
    family := .q25
    factId := 527
    role := 5
    anchorId := 258
    pointIds := [258,139]
    points := [p0208,p0139]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 528
    identity := "35a4f9adb5d29c4be130b685a367a9c1fe34f69622885655c092d1840d70f094" }
  checked := by decide +kernel

theorem w0039_check : PointSegmentLeaf.check w0039.data.points
    (Quadratic3.ofRat w0039.data.radiusSquared) w0039.data.witness = true := w0039.checked

def w0040 : CheckedWitness where
  data := {
    family := .q25
    factId := 532
    role := 5
    anchorId := 258
    pointIds := [258,140]
    points := [p0208,p0140]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 533
    identity := "b4eac4a6b50e9abaafdd98ee2c2280a423e17594eafb0ffb21521e540ebe2080" }
  checked := by decide +kernel

theorem w0040_check : PointSegmentLeaf.check w0040.data.points
    (Quadratic3.ofRat w0040.data.radiusSquared) w0040.data.witness = true := w0040.checked

def w0041 : CheckedWitness where
  data := {
    family := .q25
    factId := 536
    role := 5
    anchorId := 258
    pointIds := [258,141]
    points := [p0208,p0141]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 537
    identity := "7bebdd2074095394a41eda3cef693eaf5e0cade64f4a78caa95f0fcf83d5594b" }
  checked := by decide +kernel

theorem w0041_check : PointSegmentLeaf.check w0041.data.points
    (Quadratic3.ofRat w0041.data.radiusSquared) w0041.data.witness = true := w0041.checked

def w0042 : CheckedWitness where
  data := {
    family := .q25
    factId := 540
    role := 5
    anchorId := 258
    pointIds := [258,142]
    points := [p0208,p0142]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 541
    identity := "7e466ff45fdae9ed099ae286f5863f7a0adc37e35e22d312774a1861b285cfdd" }
  checked := by decide +kernel

theorem w0042_check : PointSegmentLeaf.check w0042.data.points
    (Quadratic3.ofRat w0042.data.radiusSquared) w0042.data.witness = true := w0042.checked

def w0043 : CheckedWitness where
  data := {
    family := .q25
    factId := 580
    role := 5
    anchorId := 258
    pointIds := [258,152]
    points := [p0208,p0152]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 581
    identity := "cb46cc0d3b3b7ec2b61d7e357cbc00aaa2d39a2153042b03c9e84e3e544cf966" }
  checked := by decide +kernel

theorem w0043_check : PointSegmentLeaf.check w0043.data.points
    (Quadratic3.ofRat w0043.data.radiusSquared) w0043.data.witness = true := w0043.checked

def w0044 : CheckedWitness where
  data := {
    family := .q25
    factId := 584
    role := 5
    anchorId := 258
    pointIds := [258,153]
    points := [p0208,p0153]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 585
    identity := "fab14c464b69b21064e3228ee27e794afbf9073f95b405fe69b5b59dfbfc7f2f" }
  checked := by decide +kernel

theorem w0044_check : PointSegmentLeaf.check w0044.data.points
    (Quadratic3.ofRat w0044.data.radiusSquared) w0044.data.witness = true := w0044.checked

def w0045 : CheckedWitness where
  data := {
    family := .q25
    factId := 588
    role := 5
    anchorId := 258
    pointIds := [258,154]
    points := [p0208,p0154]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 589
    identity := "f2ecc8359823dc286efd783dc3ef4209c740fff8a4eb5b69c390a3bf05185205" }
  checked := by decide +kernel

theorem w0045_check : PointSegmentLeaf.check w0045.data.points
    (Quadratic3.ofRat w0045.data.radiusSquared) w0045.data.witness = true := w0045.checked

def w0046 : CheckedWitness where
  data := {
    family := .q25
    factId := 592
    role := 5
    anchorId := 258
    pointIds := [258,155]
    points := [p0208,p0155]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 593
    identity := "d5bf6ddf389693cae9256fbafb82d60d296b131e94a77c2e2d5883059e8f0fdb" }
  checked := by decide +kernel

theorem w0046_check : PointSegmentLeaf.check w0046.data.points
    (Quadratic3.ofRat w0046.data.radiusSquared) w0046.data.witness = true := w0046.checked

def w0047 : CheckedWitness where
  data := {
    family := .q25
    factId := 596
    role := 5
    anchorId := 258
    pointIds := [258,156]
    points := [p0208,p0156]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 597
    identity := "0c208ae658e79eddb9726eebf11b1ed3bfc29742c14d9864f8c4c14c361be9a1" }
  checked := by decide +kernel

theorem w0047_check : PointSegmentLeaf.check w0047.data.points
    (Quadratic3.ofRat w0047.data.radiusSquared) w0047.data.witness = true := w0047.checked

def w0048 : CheckedWitness where
  data := {
    family := .q25
    factId := 600
    role := 5
    anchorId := 258
    pointIds := [258,157]
    points := [p0208,p0157]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 601
    identity := "9f44d2e7f9ca48d1e33e6b123ea0a67287c9e1e3998b78362af170641c146506" }
  checked := by decide +kernel

theorem w0048_check : PointSegmentLeaf.check w0048.data.points
    (Quadratic3.ofRat w0048.data.radiusSquared) w0048.data.witness = true := w0048.checked

def w0049 : CheckedWitness where
  data := {
    family := .q25
    factId := 638
    role := 5
    anchorId := 258
    pointIds := [258,167]
    points := [p0208,p0167]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 639
    identity := "ac70bdbe4b8d64e10bcb4b569cc6155df5b114a7323b7334e4a99293feddfaf7" }
  checked := by decide +kernel

theorem w0049_check : PointSegmentLeaf.check w0049.data.points
    (Quadratic3.ofRat w0049.data.radiusSquared) w0049.data.witness = true := w0049.checked

def w0050 : CheckedWitness where
  data := {
    family := .q25
    factId := 643
    role := 5
    anchorId := 258
    pointIds := [258,168]
    points := [p0208,p0168]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 644
    identity := "59f03fc9b055a7351f74a30a3a961501a47fa7a10674d289f6f48c954f1de0d5" }
  checked := by decide +kernel

theorem w0050_check : PointSegmentLeaf.check w0050.data.points
    (Quadratic3.ofRat w0050.data.radiusSquared) w0050.data.witness = true := w0050.checked

def w0051 : CheckedWitness where
  data := {
    family := .q25
    factId := 647
    role := 5
    anchorId := 258
    pointIds := [258,169]
    points := [p0208,p0169]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 648
    identity := "c54aad9470c050fc21ed713430e05a888e363731f38a38990876504ccf2185c0" }
  checked := by decide +kernel

theorem w0051_check : PointSegmentLeaf.check w0051.data.points
    (Quadratic3.ofRat w0051.data.radiusSquared) w0051.data.witness = true := w0051.checked

def w0052 : CheckedWitness where
  data := {
    family := .q25
    factId := 823
    role := 5
    anchorId := 258
    pointIds := [258,217]
    points := [p0208,p0217]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 824
    identity := "0e1cc639141619216b806e6d2f19cf90b3d8437b584e9bc99cd0d694796d4336" }
  checked := by decide +kernel

theorem w0052_check : PointSegmentLeaf.check w0052.data.points
    (Quadratic3.ofRat w0052.data.radiusSquared) w0052.data.witness = true := w0052.checked

def w0053 : CheckedWitness where
  data := {
    family := .q25
    factId := 827
    role := 5
    anchorId := 258
    pointIds := [258,218]
    points := [p0208,p0218]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 828
    identity := "60309eab5e4c24c1134f6bfd20fdc12499884deff4277919b688648a528c0443" }
  checked := by decide +kernel

theorem w0053_check : PointSegmentLeaf.check w0053.data.points
    (Quadratic3.ofRat w0053.data.radiusSquared) w0053.data.witness = true := w0053.checked

def w0054 : CheckedWitness where
  data := {
    family := .q25
    factId := 836
    role := 2
    anchorId := 255
    pointIds := [255,221]
    points := [p0008,p0221]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 837
    identity := "f83377e84de9d96963ccbe08d41b6fab16e9bf7bc09cdbb33b319e8a0dc4a0f9" }
  checked := by decide +kernel

theorem w0054_check : PointSegmentLeaf.check w0054.data.points
    (Quadratic3.ofRat w0054.data.radiusSquared) w0054.data.witness = true := w0054.checked

def w0055 : CheckedWitness where
  data := {
    family := .q25
    factId := 840
    role := 2
    anchorId := 255
    pointIds := [255,222]
    points := [p0008,p0222]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 841
    identity := "0fb1fe70c1aa23901cee89d11ec8846009265bf5454bafddef8eb7ab963b251d" }
  checked := by decide +kernel

theorem w0055_check : PointSegmentLeaf.check w0055.data.points
    (Quadratic3.ofRat w0055.data.radiusSquared) w0055.data.witness = true := w0055.checked

def w0056 : CheckedWitness where
  data := {
    family := .q25
    factId := 844
    role := 2
    anchorId := 255
    pointIds := [255,223]
    points := [p0008,p0223]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 845
    identity := "9e092eb85665f35ccf5d8772ff534b27437d36d27f3e4c98bc3906bd2452bd1e" }
  checked := by decide +kernel

theorem w0056_check : PointSegmentLeaf.check w0056.data.points
    (Quadratic3.ofRat w0056.data.radiusSquared) w0056.data.witness = true := w0056.checked

def w0057 : CheckedWitness where
  data := {
    family := .q25
    factId := 848
    role := 2
    anchorId := 255
    pointIds := [255,224]
    points := [p0008,p0224]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 849
    identity := "7ae229fb85ad876583c8f0eb4a4a3959080f8d3a6eba78b4b16dab0474e0a512" }
  checked := by decide +kernel

theorem w0057_check : PointSegmentLeaf.check w0057.data.points
    (Quadratic3.ofRat w0057.data.radiusSquared) w0057.data.witness = true := w0057.checked

def w0058 : CheckedWitness where
  data := {
    family := .q25
    factId := 853
    role := 2
    anchorId := 255
    pointIds := [255,225]
    points := [p0008,p0225]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 854
    identity := "d8d15f49bebf3e4a17e53a5cf01c4894417ce575df1dc21bac01f06b317b006d" }
  checked := by decide +kernel

theorem w0058_check : PointSegmentLeaf.check w0058.data.points
    (Quadratic3.ofRat w0058.data.radiusSquared) w0058.data.witness = true := w0058.checked

def w0059 : CheckedWitness where
  data := {
    family := .q25
    factId := 858
    role := 2
    anchorId := 255
    pointIds := [255,226]
    points := [p0008,p0226]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 859
    identity := "f6bef92f75ed044cfe10b11f01341b8bccd0ea2c7c3f378fdfd7185513dd3a16" }
  checked := by decide +kernel

theorem w0059_check : PointSegmentLeaf.check w0059.data.points
    (Quadratic3.ofRat w0059.data.radiusSquared) w0059.data.witness = true := w0059.checked

def w0060 : CheckedWitness where
  data := {
    family := .q25
    factId := 863
    role := 2
    anchorId := 255
    pointIds := [255,227]
    points := [p0008,p0227]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 864
    identity := "775594fe8c9565b61953c5e12f71c014c34ce9d4e4def4d7e42fc1ca027066bb" }
  checked := by decide +kernel

theorem w0060_check : PointSegmentLeaf.check w0060.data.points
    (Quadratic3.ofRat w0060.data.radiusSquared) w0060.data.witness = true := w0060.checked

def w0061 : CheckedWitness where
  data := {
    family := .q25
    factId := 867
    role := 2
    anchorId := 255
    pointIds := [255,228]
    points := [p0008,p0228]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 868
    identity := "c5d37b5c6f3ac5b9a9889de46d48bdaf11a4ff653f3061a701c4a35fca969984" }
  checked := by decide +kernel

theorem w0061_check : PointSegmentLeaf.check w0061.data.points
    (Quadratic3.ofRat w0061.data.radiusSquared) w0061.data.witness = true := w0061.checked

def w0062 : CheckedWitness where
  data := {
    family := .q25
    factId := 871
    role := 2
    anchorId := 255
    pointIds := [255,229]
    points := [p0008,p0229]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 872
    identity := "0b294b3f17a5136c8ada98c80b83064f0937143202358924293d78dd18655211" }
  checked := by decide +kernel

theorem w0062_check : PointSegmentLeaf.check w0062.data.points
    (Quadratic3.ofRat w0062.data.radiusSquared) w0062.data.witness = true := w0062.checked

def w0063 : CheckedWitness where
  data := {
    family := .q25
    factId := 875
    role := 2
    anchorId := 255
    pointIds := [255,230]
    points := [p0008,p0230]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 876
    identity := "16538d41bb313abdbd8de1a2e78b2e881a74528532a584602da2186d8d894552" }
  checked := by decide +kernel

theorem w0063_check : PointSegmentLeaf.check w0063.data.points
    (Quadratic3.ofRat w0063.data.radiusSquared) w0063.data.witness = true := w0063.checked

def w0064 : CheckedWitness where
  data := {
    family := .q25
    factId := 880
    role := 2
    anchorId := 255
    pointIds := [255,231]
    points := [p0008,p0231]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 881
    identity := "e36b858efc4780e85a30172553ce003ba487ad9dc4a72c9e54dcd68d12515e6a" }
  checked := by decide +kernel

theorem w0064_check : PointSegmentLeaf.check w0064.data.points
    (Quadratic3.ofRat w0064.data.radiusSquared) w0064.data.witness = true := w0064.checked

def w0065 : CheckedWitness where
  data := {
    family := .q25
    factId := 885
    role := 2
    anchorId := 255
    pointIds := [255,232]
    points := [p0008,p0232]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 886
    identity := "de3f777b2688d9694b389664521680caf5d514b461779a2aa07de6890beac6e1" }
  checked := by decide +kernel

theorem w0065_check : PointSegmentLeaf.check w0065.data.points
    (Quadratic3.ofRat w0065.data.radiusSquared) w0065.data.witness = true := w0065.checked

def w0066 : CheckedWitness where
  data := {
    family := .q25
    factId := 890
    role := 2
    anchorId := 255
    pointIds := [255,233]
    points := [p0008,p0233]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 891
    identity := "2fda3f669f0828f61694778e25183a6eaa4629b42982d52d30b4e76029888fab" }
  checked := by decide +kernel

theorem w0066_check : PointSegmentLeaf.check w0066.data.points
    (Quadratic3.ofRat w0066.data.radiusSquared) w0066.data.witness = true := w0066.checked

def w0067 : CheckedWitness where
  data := {
    family := .q25
    factId := 894
    role := 2
    anchorId := 255
    pointIds := [255,234]
    points := [p0008,p0234]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 895
    identity := "fe6e668caa020e0df6fbf3d17a99e20d6217b005178d72e8c07fabc16c90693b" }
  checked := by decide +kernel

theorem w0067_check : PointSegmentLeaf.check w0067.data.points
    (Quadratic3.ofRat w0067.data.radiusSquared) w0067.data.witness = true := w0067.checked

def w0068 : CheckedWitness where
  data := {
    family := .q25
    factId := 898
    role := 2
    anchorId := 255
    pointIds := [255,235]
    points := [p0008,p0235]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 899
    identity := "698bfc1f640862b7249ced0a9eee7908c5fb1da6e0404d0367956334657210af" }
  checked := by decide +kernel

theorem w0068_check : PointSegmentLeaf.check w0068.data.points
    (Quadratic3.ofRat w0068.data.radiusSquared) w0068.data.witness = true := w0068.checked

def w0069 : CheckedWitness where
  data := {
    family := .q25
    factId := 902
    role := 2
    anchorId := 255
    pointIds := [255,236]
    points := [p0008,p0236]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 903
    identity := "0b2eb2f98f389ba61d43827f112d9d641cde4e21272d68f1df92bdd0a45013ec" }
  checked := by decide +kernel

theorem w0069_check : PointSegmentLeaf.check w0069.data.points
    (Quadratic3.ofRat w0069.data.radiusSquared) w0069.data.witness = true := w0069.checked

def w0070 : CheckedWitness where
  data := {
    family := .q25
    factId := 915
    role := 5
    anchorId := 258
    pointIds := [258,239]
    points := [p0208,p0239]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 916
    identity := "c585e490662e1c24cf3e194b692d11ae2f74c477fb812cf311d1caa9bc64417a" }
  checked := by decide +kernel

theorem w0070_check : PointSegmentLeaf.check w0070.data.points
    (Quadratic3.ofRat w0070.data.radiusSquared) w0070.data.witness = true := w0070.checked

def w0071 : CheckedWitness where
  data := {
    family := .q25
    factId := 919
    role := 5
    anchorId := 258
    pointIds := [258,240]
    points := [p0208,p0240]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 920
    identity := "91aa0bd9ded5a3836cf9c74e388e7e71a4785676e80401e9296e784c7d1845bb" }
  checked := by decide +kernel

theorem w0071_check : PointSegmentLeaf.check w0071.data.points
    (Quadratic3.ofRat w0071.data.radiusSquared) w0071.data.witness = true := w0071.checked

def w0072 : CheckedWitness where
  data := {
    family := .q25
    factId := 923
    role := 5
    anchorId := 258
    pointIds := [258,241]
    points := [p0208,p0241]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 924
    identity := "c94a74dd1c78769e8853352eccfdbb60983e262cd8d2f5b63c96eca02011ce8d" }
  checked := by decide +kernel

theorem w0072_check : PointSegmentLeaf.check w0072.data.points
    (Quadratic3.ofRat w0072.data.radiusSquared) w0072.data.witness = true := w0072.checked

def w0073 : CheckedWitness where
  data := {
    family := .q25
    factId := 927
    role := 5
    anchorId := 258
    pointIds := [258,242]
    points := [p0208,p0242]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 928
    identity := "d3bafdd5e7984ef078fd703c189c46671fc7cef0fb54918039aad139d366be68" }
  checked := by decide +kernel

theorem w0073_check : PointSegmentLeaf.check w0073.data.points
    (Quadratic3.ofRat w0073.data.radiusSquared) w0073.data.witness = true := w0073.checked

def w0074 : CheckedWitness where
  data := {
    family := .q25
    factId := 932
    role := 5
    anchorId := 258
    pointIds := [258,243]
    points := [p0208,p0243]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 933
    identity := "7c5c12b41a83bbe78081233f34638c102cd98d174ef9f8156e46b4550acd1cdf" }
  checked := by decide +kernel

theorem w0074_check : PointSegmentLeaf.check w0074.data.points
    (Quadratic3.ofRat w0074.data.radiusSquared) w0074.data.witness = true := w0074.checked

def w0075 : CheckedWitness where
  data := {
    family := .q25
    factId := 937
    role := 5
    anchorId := 258
    pointIds := [258,244]
    points := [p0208,p0244]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 938
    identity := "673b66dd8226f7c2760168ca58f0fe0298fe36b30b30c07f030512dbaa44e168" }
  checked := by decide +kernel

theorem w0075_check : PointSegmentLeaf.check w0075.data.points
    (Quadratic3.ofRat w0075.data.radiusSquared) w0075.data.witness = true := w0075.checked

def w0076 : CheckedWitness where
  data := {
    family := .q25
    factId := 941
    role := 5
    anchorId := 258
    pointIds := [258,245]
    points := [p0208,p0245]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 942
    identity := "e023f7d7a7bfca1d5476aa4c1b558cdf22bf9ccb186c770f7be131056de2b596" }
  checked := by decide +kernel

theorem w0076_check : PointSegmentLeaf.check w0076.data.points
    (Quadratic3.ofRat w0076.data.radiusSquared) w0076.data.witness = true := w0076.checked

def w0077 : CheckedWitness where
  data := {
    family := .q25
    factId := 945
    role := 5
    anchorId := 258
    pointIds := [258,246]
    points := [p0208,p0246]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 946
    identity := "bc8f75c12e510291139baf32fb0ab9b8c776d527c520e8f719b6c198b1d2e8be" }
  checked := by decide +kernel

theorem w0077_check : PointSegmentLeaf.check w0077.data.points
    (Quadratic3.ofRat w0077.data.radiusSquared) w0077.data.witness = true := w0077.checked

def w0078 : CheckedWitness where
  data := {
    family := .q25
    factId := 949
    role := 5
    anchorId := 258
    pointIds := [258,247]
    points := [p0208,p0247]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 950
    identity := "9f9485632a6f59b01a2369640e29263c7085f1d76b06bb9ecb49eb3813d6b123" }
  checked := by decide +kernel

theorem w0078_check : PointSegmentLeaf.check w0078.data.points
    (Quadratic3.ofRat w0078.data.radiusSquared) w0078.data.witness = true := w0078.checked

def w0079 : CheckedWitness where
  data := {
    family := .q25
    factId := 953
    role := 5
    anchorId := 258
    pointIds := [258,248]
    points := [p0208,p0248]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 954
    identity := "29703feebea9c9f0c0595db634f508c738972754b1f2589a5d0d2566445fd3f6" }
  checked := by decide +kernel

theorem w0079_check : PointSegmentLeaf.check w0079.data.points
    (Quadratic3.ofRat w0079.data.radiusSquared) w0079.data.witness = true := w0079.checked

def w0080 : CheckedWitness where
  data := {
    family := .q25
    factId := 958
    role := 5
    anchorId := 258
    pointIds := [258,249]
    points := [p0208,p0249]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 959
    identity := "427b51b10e925108ea409b77ba93f2de83411b8656e9d176628cd9aa1d5838e7" }
  checked := by decide +kernel

theorem w0080_check : PointSegmentLeaf.check w0080.data.points
    (Quadratic3.ofRat w0080.data.radiusSquared) w0080.data.witness = true := w0080.checked

def w0081 : CheckedWitness where
  data := {
    family := .q25
    factId := 963
    role := 5
    anchorId := 258
    pointIds := [258,250]
    points := [p0208,p0250]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 964
    identity := "c5c6376418907f0fc6716786f223f2615837242f016f4d1c4d203f0abdefe810" }
  checked := by decide +kernel

theorem w0081_check : PointSegmentLeaf.check w0081.data.points
    (Quadratic3.ofRat w0081.data.radiusSquared) w0081.data.witness = true := w0081.checked

def w0082 : CheckedWitness where
  data := {
    family := .q25
    factId := 967
    role := 5
    anchorId := 258
    pointIds := [258,251]
    points := [p0208,p0251]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 968
    identity := "08b2f0f0326e467c753d94dc9c19e0b923c7cebd297faa173baa37c40654e689" }
  checked := by decide +kernel

theorem w0082_check : PointSegmentLeaf.check w0082.data.points
    (Quadratic3.ofRat w0082.data.radiusSquared) w0082.data.witness = true := w0082.checked

def w0083 : CheckedWitness where
  data := {
    family := .q25
    factId := 971
    role := 5
    anchorId := 258
    pointIds := [258,252]
    points := [p0208,p0252]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 972
    identity := "dc9563ed46984d324d759a1959a41eb787e2f2db89d42bf9b991c0c600d65112" }
  checked := by decide +kernel

theorem w0083_check : PointSegmentLeaf.check w0083.data.points
    (Quadratic3.ofRat w0083.data.radiusSquared) w0083.data.witness = true := w0083.checked

def w0084 : CheckedWitness where
  data := {
    family := .q25
    factId := 1024
    role := 2
    anchorId := 255
    pointIds := [255,7,16,112]
    points := [p0008,p0007,p0016,p0112]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 1025
    identity := "2d3faf0b05b071ed6dd14524686884932a793438702a501818d21401e8bb7231" }
  checked := by decide +kernel

theorem w0084_check : PointSegmentLeaf.check w0084.data.points
    (Quadratic3.ofRat w0084.data.radiusSquared) w0084.data.witness = true := w0084.checked

def w0085 : CheckedWitness where
  data := {
    family := .q25
    factId := 1045
    role := 5
    anchorId := 258
    pointIds := [258,104,200,209]
    points := [p0208,p0104,p0200,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 1046
    identity := "b40ad0779d0c3db1bfeb50f96a61b739c8b79e6235c584204f58501611f39c89" }
  checked := by decide +kernel

theorem w0085_check : PointSegmentLeaf.check w0085.data.points
    (Quadratic3.ofRat w0085.data.radiusSquared) w0085.data.witness = true := w0085.checked

def w0086 : CheckedWitness where
  data := {
    family := .q25
    factId := 1402
    role := 2
    anchorId := 255
    pointIds := [255,5,6,7,8,15,16,17,18,26,27,38,46]
    points := [p0008,p0005,p0006,p0007,p0008,p0015,p0016,p0017,p0018,p0026,p0027,p0038,p0046]
    radiusSquared := 1/4
    witness := .segment 7 12
    originalFlag := false
    sourceNI := true
    journalLine := 1403
    identity := "503af1122e956ec0088c9f0b5632e58bf67955e2533373c5b228143fad823bbb" }
  checked := by decide +kernel

theorem w0086_check : PointSegmentLeaf.check w0086.data.points
    (Quadratic3.ofRat w0086.data.radiusSquared) w0086.data.witness = true := w0086.checked

def w0087 : CheckedWitness where
  data := {
    family := .q25
    factId := 1754
    role := 2
    anchorId := 255
    pointIds := [255,7,8,16,17,18,29,46]
    points := [p0008,p0007,p0008,p0016,p0017,p0018,p0029,p0046]
    radiusSquared := 1/4
    witness := .segment 4 7
    originalFlag := false
    sourceNI := true
    journalLine := 1755
    identity := "ccbf1ee970052a49bb4e317da1f0887c427fad6cdb350fd96c1a2f02ce1beffe" }
  checked := by decide +kernel

theorem w0087_check : PointSegmentLeaf.check w0087.data.points
    (Quadratic3.ofRat w0087.data.radiusSquared) w0087.data.witness = true := w0087.checked

def w0088 : CheckedWitness where
  data := {
    family := .q25
    factId := 2152
    role := 2
    anchorId := 255
    pointIds := [255,5,6,7,8,15,16,17,26,27,38,46]
    points := [p0008,p0005,p0006,p0007,p0008,p0015,p0016,p0017,p0026,p0027,p0038,p0046]
    radiusSquared := 1/4
    witness := .segment 7 11
    originalFlag := false
    sourceNI := true
    journalLine := 2153
    identity := "9efc5c805c2e0074f0229638862c2d8db2d153ac85ece4589f01ac4df0ebffd7" }
  checked := by decide +kernel

theorem w0088_check : PointSegmentLeaf.check w0088.data.points
    (Quadratic3.ofRat w0088.data.radiusSquared) w0088.data.witness = true := w0088.checked

def w0089 : CheckedWitness where
  data := {
    family := .q25
    factId := 2229
    role := 2
    anchorId := 255
    pointIds := [255,7,8,16,17,18,28,46]
    points := [p0008,p0007,p0008,p0016,p0017,p0018,p0028,p0046]
    radiusSquared := 1/4
    witness := .segment 4 7
    originalFlag := false
    sourceNI := true
    journalLine := 2230
    identity := "700d795fe22512cfacec3ace753f81e9d656792c3e6944e8a81be1d21d38d537" }
  checked := by decide +kernel

theorem w0089_check : PointSegmentLeaf.check w0089.data.points
    (Quadratic3.ofRat w0089.data.radiusSquared) w0089.data.witness = true := w0089.checked

def w0090 : CheckedWitness where
  data := {
    family := .q25
    factId := 2321
    role := 2
    anchorId := 255
    pointIds := [255,7,8,16,17,18,27,28,46]
    points := [p0008,p0007,p0008,p0016,p0017,p0018,p0027,p0028,p0046]
    radiusSquared := 1/4
    witness := .segment 4 8
    originalFlag := false
    sourceNI := true
    journalLine := 2322
    identity := "217b514dd2cf054424ad053087c4563dbf416c12c89a54932e96418608dc1e4f" }
  checked := by decide +kernel

theorem w0090_check : PointSegmentLeaf.check w0090.data.points
    (Quadratic3.ofRat w0090.data.radiusSquared) w0090.data.witness = true := w0090.checked

def w0091 : CheckedWitness where
  data := {
    family := .q25
    factId := 3439
    role := 5
    anchorId := 258
    pointIds := [258,104,177,178,187,189,198,199,208,209]
    points := [p0208,p0104,p0177,p0178,p0187,p0189,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 3440
    identity := "b286ca4cf8a0688bd79f9c2f5224388f3e693ac52b60a9e7ae4ef6e1981be0ae" }
  checked := by decide +kernel

theorem w0091_check : PointSegmentLeaf.check w0091.data.points
    (Quadratic3.ofRat w0091.data.radiusSquared) w0091.data.witness = true := w0091.checked

def w0092 : CheckedWitness where
  data := {
    family := .q25
    factId := 3934
    role := 5
    anchorId := 258
    pointIds := [258,104,117,189,199,208]
    points := [p0208,p0104,p0117,p0189,p0199,p0208]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 3935
    identity := "a77cfc466c35d4d7e40159d54c084a84d32d30410ba5ea16ee163aed4867d432" }
  checked := by decide +kernel

theorem w0092_check : PointSegmentLeaf.check w0092.data.points
    (Quadratic3.ofRat w0092.data.radiusSquared) w0092.data.witness = true := w0092.checked

def w0093 : CheckedWitness where
  data := {
    family := .q25
    factId := 4242
    role := 5
    anchorId := 258
    pointIds := [258,162,170]
    points := [p0208,p0162,p0170]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 4243
    identity := "c10fbfc987bae9d18f24dd5f030c8251527190a836c70fc1557f560cc3d04148" }
  checked := by decide +kernel

theorem w0093_check : PointSegmentLeaf.check w0093.data.points
    (Quadratic3.ofRat w0093.data.radiusSquared) w0093.data.witness = true := w0093.checked

def w0094 : CheckedWitness where
  data := {
    family := .q25
    factId := 4589
    role := 2
    anchorId := 255
    pointIds := [255,8,17,18,27,29,46]
    points := [p0008,p0008,p0017,p0018,p0027,p0029,p0046]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 4590
    identity := "03adb2f980304a2ff69a158d6fd654a5677aca6e0bb5ee69c0136bed1c38c4f4" }
  checked := by decide +kernel

theorem w0094_check : PointSegmentLeaf.check w0094.data.points
    (Quadratic3.ofRat w0094.data.radiusSquared) w0094.data.witness = true := w0094.checked

def w0095 : CheckedWitness where
  data := {
    family := .q25
    factId := 4751
    role := 2
    anchorId := 255
    pointIds := [255,7,8,17,18,27,28,46]
    points := [p0008,p0007,p0008,p0017,p0018,p0027,p0028,p0046]
    radiusSquared := 1/4
    witness := .segment 3 7
    originalFlag := false
    sourceNI := true
    journalLine := 4752
    identity := "7ac99f69fc235614fdecbf937a1551d7f1ced4539dfe2c81f8c440c107be4d31" }
  checked := by decide +kernel

theorem w0095_check : PointSegmentLeaf.check w0095.data.points
    (Quadratic3.ofRat w0095.data.radiusSquared) w0095.data.witness = true := w0095.checked

def w0096 : CheckedWitness where
  data := {
    family := .q25
    factId := 4760
    role := 2
    anchorId := 255
    pointIds := [255,7,8,17,18,27,28,29,38,40,41,112]
    points := [p0008,p0007,p0008,p0017,p0018,p0027,p0028,p0029,p0038,p0040,p0041,p0112]
    radiusSquared := 1/4
    witness := .segment 1 11
    originalFlag := false
    sourceNI := true
    journalLine := 4761
    identity := "2ea10241c330ef8c84391a2be610ee21ee8e1b72faa19817bd8cbb253b07e00a" }
  checked := by decide +kernel

theorem w0096_check : PointSegmentLeaf.check w0096.data.points
    (Quadratic3.ofRat w0096.data.radiusSquared) w0096.data.witness = true := w0096.checked

def w0097 : CheckedWitness where
  data := {
    family := .q25
    factId := 4804
    role := 5
    anchorId := 258
    pointIds := [258,104,198,199,208,209,210]
    points := [p0208,p0104,p0198,p0199,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 4805
    identity := "59debfa725bd739b518468d71161a375a59a83bc94226f2fd0ebc40d36f4a27a" }
  checked := by decide +kernel

theorem w0097_check : PointSegmentLeaf.check w0097.data.points
    (Quadratic3.ofRat w0097.data.radiusSquared) w0097.data.witness = true := w0097.checked

def w0098 : CheckedWitness where
  data := {
    family := .q25
    factId := 4821
    role := 2
    anchorId := 255
    pointIds := [255,7,8,17,18,27,28,29,38,39,40,41,112]
    points := [p0008,p0007,p0008,p0017,p0018,p0027,p0028,p0029,p0038,p0039,p0040,p0041,p0112]
    radiusSquared := 1/4
    witness := .segment 1 12
    originalFlag := false
    sourceNI := true
    journalLine := 4822
    identity := "efee8fb6deab465698a638521a526396bc56f64d9cb8cb0818987b3c5a8fa7c8" }
  checked := by decide +kernel

theorem w0098_check : PointSegmentLeaf.check w0098.data.points
    (Quadratic3.ofRat w0098.data.radiusSquared) w0098.data.witness = true := w0098.checked

def w0099 : CheckedWitness where
  data := {
    family := .q25
    factId := 4892
    role := 2
    anchorId := 255
    pointIds := [255,7,8,17,18,27,28,29,38,40,112]
    points := [p0008,p0007,p0008,p0017,p0018,p0027,p0028,p0029,p0038,p0040,p0112]
    radiusSquared := 1/4
    witness := .segment 1 10
    originalFlag := false
    sourceNI := true
    journalLine := 4893
    identity := "d378401de5fb345f058ec2bebd47af721386f22c7ad569e5d993d31a8704f551" }
  checked := by decide +kernel

theorem w0099_check : PointSegmentLeaf.check w0099.data.points
    (Quadratic3.ofRat w0099.data.radiusSquared) w0099.data.witness = true := w0099.checked

def w0100 : CheckedWitness where
  data := {
    family := .q25
    factId := 4916
    role := 5
    anchorId := 258
    pointIds := [258,104,198,208,209,210]
    points := [p0208,p0104,p0198,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 4917
    identity := "f531b953c2f5c9cd356f1408611208b9596441d51facdce29d7d2a5c64a38a2c" }
  checked := by decide +kernel

theorem w0100_check : PointSegmentLeaf.check w0100.data.points
    (Quadratic3.ofRat w0100.data.radiusSquared) w0100.data.witness = true := w0100.checked

def w0101 : CheckedWitness where
  data := {
    family := .q25
    factId := 4961
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198,208,209,210]
    points := [p0208,p0170,p0187,p0198,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 4962
    identity := "dcb6e4f8f3ca5ba99e677d27ea76700a54375e765efc78d6a358f95c53f75337" }
  checked := by decide +kernel

theorem w0101_check : PointSegmentLeaf.check w0101.data.points
    (Quadratic3.ofRat w0101.data.radiusSquared) w0101.data.witness = true := w0101.checked

def w0102 : CheckedWitness where
  data := {
    family := .q25
    factId := 5245
    role := 5
    anchorId := 258
    pointIds := [258,104,162,163,164,175,187,189,198,200,208,209]
    points := [p0208,p0104,p0162,p0163,p0164,p0175,p0187,p0189,p0198,p0200,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 5246
    identity := "45b65f9b04b550f7dd299fe9a76119c5689592c84416fff8213030e771f954a8" }
  checked := by decide +kernel

theorem w0102_check : PointSegmentLeaf.check w0102.data.points
    (Quadratic3.ofRat w0102.data.radiusSquared) w0102.data.witness = true := w0102.checked

def w0103 : CheckedWitness where
  data := {
    family := .q25
    factId := 5419
    role := 2
    anchorId := 255
    pointIds := [255,8,17,18,27,28,46]
    points := [p0008,p0008,p0017,p0018,p0027,p0028,p0046]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 5420
    identity := "e3b9bc0cb8543e7022f146dd59d3f4fc718ec78a341583b11e13e2590515c42e" }
  checked := by decide +kernel

theorem w0103_check : PointSegmentLeaf.check w0103.data.points
    (Quadratic3.ofRat w0103.data.radiusSquared) w0103.data.witness = true := w0103.checked

def w0104 : CheckedWitness where
  data := {
    family := .q25
    factId := 5738
    role := 2
    anchorId := 255
    pointIds := [255,7,8,18,28,46]
    points := [p0008,p0007,p0008,p0018,p0028,p0046]
    radiusSquared := 1/4
    witness := .segment 3 5
    originalFlag := false
    sourceNI := true
    journalLine := 5739
    identity := "3c6821cac10d5429e4a2714c0e74bab48d20f9632726dd010f0ad979431b9ef3" }
  checked := by decide +kernel

theorem w0104_check : PointSegmentLeaf.check w0104.data.points
    (Quadratic3.ofRat w0104.data.radiusSquared) w0104.data.witness = true := w0104.checked

def w0105 : CheckedWitness where
  data := {
    family := .q25
    factId := 7332
    role := 5
    anchorId := 258
    pointIds := [258,170,188,189,198,199,208,209]
    points := [p0208,p0170,p0188,p0189,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 7333
    identity := "adf269e781271fc141dc8751c71abf27923d0da74780f2e39aecd095d40e540f" }
  checked := by decide +kernel

theorem w0105_check : PointSegmentLeaf.check w0105.data.points
    (Quadratic3.ofRat w0105.data.radiusSquared) w0105.data.witness = true := w0105.checked

def w0106 : CheckedWitness where
  data := {
    family := .q25
    factId := 7345
    role := 5
    anchorId := 258
    pointIds := [258,104,178,188,189,198,199,208,209]
    points := [p0208,p0104,p0178,p0188,p0189,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 7346
    identity := "a37b436fa00d1e26f05eae2d31133df4e73fb75f261eafea128a9eb7593b412c" }
  checked := by decide +kernel

theorem w0106_check : PointSegmentLeaf.check w0106.data.points
    (Quadratic3.ofRat w0106.data.radiusSquared) w0106.data.witness = true := w0106.checked

def w0107 : CheckedWitness where
  data := {
    family := .q25
    factId := 7503
    role := 2
    anchorId := 255
    pointIds := [255,6,7,8,18,112]
    points := [p0008,p0006,p0007,p0008,p0018,p0112]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 7504
    identity := "195b2362bbf3d4b1116b1d12c19dee7104fcdc80b473038d1f7ca0bc3b9258e6" }
  checked := by decide +kernel

theorem w0107_check : PointSegmentLeaf.check w0107.data.points
    (Quadratic3.ofRat w0107.data.radiusSquared) w0107.data.witness = true := w0107.checked

def w0108 : CheckedWitness where
  data := {
    family := .q25
    factId := 7518
    role := 2
    anchorId := 255
    pointIds := [255,6,7,8,16,17,18,27,28,46]
    points := [p0008,p0006,p0007,p0008,p0016,p0017,p0018,p0027,p0028,p0046]
    radiusSquared := 1/4
    witness := .segment 5 9
    originalFlag := false
    sourceNI := true
    journalLine := 7519
    identity := "bbe242f5bca026d2651fb762d0711c2daf64513a8d22dc24d136aa7a37b324c2" }
  checked := by decide +kernel

theorem w0108_check : PointSegmentLeaf.check w0108.data.points
    (Quadratic3.ofRat w0108.data.radiusSquared) w0108.data.witness = true := w0108.checked

def w0109 : CheckedWitness where
  data := {
    family := .q25
    factId := 7546
    role := 2
    anchorId := 255
    pointIds := [255,6,7,8,18,29,46]
    points := [p0008,p0006,p0007,p0008,p0018,p0029,p0046]
    radiusSquared := 1/4
    witness := .segment 4 6
    originalFlag := false
    sourceNI := true
    journalLine := 7547
    identity := "df10f74f50de2d92c93332d802cd4d9ead6dca453be66dfdb276bd62f9f19162" }
  checked := by decide +kernel

theorem w0109_check : PointSegmentLeaf.check w0109.data.points
    (Quadratic3.ofRat w0109.data.radiusSquared) w0109.data.witness = true := w0109.checked

def w0110 : CheckedWitness where
  data := {
    family := .q25
    factId := 8760
    role := 5
    anchorId := 258
    pointIds := [258,170,177,198,199,208,209]
    points := [p0208,p0170,p0177,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 8761
    identity := "0b5f88911efe29f08d81ad553f0d24e4d22f3a9f491fc741e8c2d65d008e289b" }
  checked := by decide +kernel

theorem w0110_check : PointSegmentLeaf.check w0110.data.points
    (Quadratic3.ofRat w0110.data.radiusSquared) w0110.data.witness = true := w0110.checked

def w0111 : CheckedWitness where
  data := {
    family := .q25
    factId := 9304
    role := 2
    anchorId := 255
    pointIds := [255,8,18,29,46]
    points := [p0008,p0008,p0018,p0029,p0046]
    radiusSquared := 1/4
    witness := .segment 2 4
    originalFlag := false
    sourceNI := true
    journalLine := 9305
    identity := "622a5ef7cd444bec264bd58c6efb4c962853dfe2afb8b4c47633a2438440c759" }
  checked := by decide +kernel

theorem w0111_check : PointSegmentLeaf.check w0111.data.points
    (Quadratic3.ofRat w0111.data.radiusSquared) w0111.data.witness = true := w0111.checked

def w0112 : CheckedWitness where
  data := {
    family := .q25
    factId := 9359
    role := 5
    anchorId := 258
    pointIds := [258,162,170,199,208]
    points := [p0208,p0162,p0170,p0199,p0208]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 9360
    identity := "9291c2cc8f9a89bb9fc4884d59e4d33e3e895a7853ea65510f5f8de153c327ca" }
  checked := by decide +kernel

theorem w0112_check : PointSegmentLeaf.check w0112.data.points
    (Quadratic3.ofRat w0112.data.radiusSquared) w0112.data.witness = true := w0112.checked

def w0113 : CheckedWitness where
  data := {
    family := .q25
    factId := 9854
    role := 5
    anchorId := 258
    pointIds := [258,104,178,198,199,208,209]
    points := [p0208,p0104,p0178,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 9855
    identity := "f63673f76d69933a5ec6a601ede1cebcda21864b9a5a63a5ca8e1e65eb2e8aa9" }
  checked := by decide +kernel

theorem w0113_check : PointSegmentLeaf.check w0113.data.points
    (Quadratic3.ofRat w0113.data.radiusSquared) w0113.data.witness = true := w0113.checked

def w0114 : CheckedWitness where
  data := {
    family := .q25
    factId := 10683
    role := 5
    anchorId := 258
    pointIds := [258,104,190,198,199,208,209]
    points := [p0208,p0104,p0190,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 10684
    identity := "6df71e6787c797daacaaf0a5c68a1e3464043adbee9783dfec74df254995e89c" }
  checked := by decide +kernel

theorem w0114_check : PointSegmentLeaf.check w0114.data.points
    (Quadratic3.ofRat w0114.data.radiusSquared) w0114.data.witness = true := w0114.checked

def w0115 : CheckedWitness where
  data := {
    family := .q25
    factId := 10892
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198,199,208,209,210]
    points := [p0208,p0170,p0187,p0198,p0199,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 10893
    identity := "e5a459d3ad8801ec10d12fc30fc5d523f288f9732a64ffb53438fbdbb44d4611" }
  checked := by decide +kernel

theorem w0115_check : PointSegmentLeaf.check w0115.data.points
    (Quadratic3.ofRat w0115.data.radiusSquared) w0115.data.witness = true := w0115.checked

def w0116 : CheckedWitness where
  data := {
    family := .q25
    factId := 11466
    role := 5
    anchorId := 258
    pointIds := [258,170,175,198,208,209]
    points := [p0208,p0170,p0175,p0198,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 11467
    identity := "2a4e5ae690df607556915dd0f9c9f61c9aac3600fe687fdad9782e7e05069ba1" }
  checked := by decide +kernel

theorem w0116_check : PointSegmentLeaf.check w0116.data.points
    (Quadratic3.ofRat w0116.data.radiusSquared) w0116.data.witness = true := w0116.checked

def w0117 : CheckedWitness where
  data := {
    family := .q25
    factId := 12998
    role := 2
    anchorId := 255
    pointIds := [255,6,7,8,15,17,26,27,38,46]
    points := [p0008,p0006,p0007,p0008,p0015,p0017,p0026,p0027,p0038,p0046]
    radiusSquared := 1/4
    witness := .segment 5 9
    originalFlag := false
    sourceNI := true
    journalLine := 12999
    identity := "9ea7aff339e3eabbfd3747fcc804b76ecad6f58d6bba61c06e13aecbc0710bb9" }
  checked := by decide +kernel

theorem w0117_check : PointSegmentLeaf.check w0117.data.points
    (Quadratic3.ofRat w0117.data.radiusSquared) w0117.data.witness = true := w0117.checked

def w0118 : CheckedWitness where
  data := {
    family := .q25
    factId := 13983
    role := 5
    anchorId := 258
    pointIds := [258,104,187,198,208,209,211]
    points := [p0208,p0104,p0187,p0198,p0208,p0209,p0211]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 13984
    identity := "d17c25dfb556dfb4ae35e45a2a7f1a69f7f8b921e4c814aca1ddd5e10a374395" }
  checked := by decide +kernel

theorem w0118_check : PointSegmentLeaf.check w0118.data.points
    (Quadratic3.ofRat w0118.data.radiusSquared) w0118.data.witness = true := w0118.checked

def w0119 : CheckedWitness where
  data := {
    family := .q25
    factId := 14832
    role := 2
    anchorId := 255
    pointIds := [255,3,6,7,8,16,18,26,37,46]
    points := [p0008,p0003,p0006,p0007,p0008,p0016,p0018,p0026,p0037,p0046]
    radiusSquared := 1/4
    witness := .segment 6 9
    originalFlag := false
    sourceNI := true
    journalLine := 14833
    identity := "5755d4f47ca5c6eb101252b572636f8a0700faaf0949d4ff28aefee774f7fb6f" }
  checked := by decide +kernel

theorem w0119_check : PointSegmentLeaf.check w0119.data.points
    (Quadratic3.ofRat w0119.data.radiusSquared) w0119.data.witness = true := w0119.checked

def w0120 : CheckedWitness where
  data := {
    family := .q25
    factId := 14846
    role := 2
    anchorId := 255
    pointIds := [255,5,6,7,8,15,16,18,26,38,46]
    points := [p0008,p0005,p0006,p0007,p0008,p0015,p0016,p0018,p0026,p0038,p0046]
    radiusSquared := 1/4
    witness := .segment 7 10
    originalFlag := false
    sourceNI := true
    journalLine := 14847
    identity := "d01c4cb9d9d1b8c668e4360129cf8c404e29d0778b4d2935a160bed7ac579800" }
  checked := by decide +kernel

theorem w0120_check : PointSegmentLeaf.check w0120.data.points
    (Quadratic3.ofRat w0120.data.radiusSquared) w0120.data.witness = true := w0120.checked

def w0121 : CheckedWitness where
  data := {
    family := .q25
    factId := 14863
    role := 2
    anchorId := 255
    pointIds := [255,6,7,8,16,18,26,37,46]
    points := [p0008,p0006,p0007,p0008,p0016,p0018,p0026,p0037,p0046]
    radiusSquared := 1/4
    witness := .segment 5 8
    originalFlag := false
    sourceNI := true
    journalLine := 14864
    identity := "d9becd62b61c760515cb2abf9b46a1ce2f5b6b93d80c64a30015628d8c9afe96" }
  checked := by decide +kernel

theorem w0121_check : PointSegmentLeaf.check w0121.data.points
    (Quadratic3.ofRat w0121.data.radiusSquared) w0121.data.witness = true := w0121.checked

def w0122 : CheckedWitness where
  data := {
    family := .q25
    factId := 14872
    role := 2
    anchorId := 255
    pointIds := [255,6,7,8,16,18,29,46]
    points := [p0008,p0006,p0007,p0008,p0016,p0018,p0029,p0046]
    radiusSquared := 1/4
    witness := .segment 5 7
    originalFlag := false
    sourceNI := true
    journalLine := 14873
    identity := "4bc97933938f63f25da78da64c4ba48d8f65a5daf8dd7ffaab1f076b5a82bc18" }
  checked := by decide +kernel

theorem w0122_check : PointSegmentLeaf.check w0122.data.points
    (Quadratic3.ofRat w0122.data.radiusSquared) w0122.data.witness = true := w0122.checked

def w0123 : CheckedWitness where
  data := {
    family := .q25
    factId := 16535
    role := 2
    anchorId := 255
    pointIds := [255,6,7,8,16,17,18,29,46]
    points := [p0008,p0006,p0007,p0008,p0016,p0017,p0018,p0029,p0046]
    radiusSquared := 1/4
    witness := .segment 5 8
    originalFlag := false
    sourceNI := true
    journalLine := 16536
    identity := "9a20dfcecd5a6a1cbaeae556c399cef7c7f808eb1bf1a90fc9b878546e08f1c4" }
  checked := by decide +kernel

theorem w0123_check : PointSegmentLeaf.check w0123.data.points
    (Quadratic3.ofRat w0123.data.radiusSquared) w0123.data.witness = true := w0123.checked

def w0124 : CheckedWitness where
  data := {
    family := .q25
    factId := 19336
    role := 5
    anchorId := 258
    pointIds := [258,104,190,198,208,209]
    points := [p0208,p0104,p0190,p0198,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 19337
    identity := "4ed91526c730e739896cf85ea0fe77b48ddfe3da4133df4d73a8062e233b4576" }
  checked := by decide +kernel

theorem w0124_check : PointSegmentLeaf.check w0124.data.points
    (Quadratic3.ofRat w0124.data.radiusSquared) w0124.data.witness = true := w0124.checked

def w0125 : CheckedWitness where
  data := {
    family := .q25
    factId := 24140
    role := 2
    anchorId := 255
    pointIds := [255,5,6,7,8,15,16,18,26,27,28,29,36,38,39,80]
    points := [p0008,p0005,p0006,p0007,p0008,p0015,p0016,p0018,p0026,p0027,p0028,p0029,p0036,p0038,p0039,p0080]
    radiusSquared := 1/4
    witness := .segment 12 15
    originalFlag := false
    sourceNI := true
    journalLine := 24141
    identity := "a899b1b629b8483a0bae2f255501c5b3bd5b1ad608bb27aad7bfbc57310445ba" }
  checked := by decide +kernel

theorem w0125_check : PointSegmentLeaf.check w0125.data.points
    (Quadratic3.ofRat w0125.data.radiusSquared) w0125.data.witness = true := w0125.checked

def w0126 : CheckedWitness where
  data := {
    family := .q25
    factId := 27189
    role := 2
    anchorId := 255
    pointIds := [255,3,4,5,6,7,8,14,16,18,24,25,27,28,29,35,37,38,39,40,50]
    points := [p0008,p0003,p0004,p0005,p0006,p0007,p0008,p0014,p0016,p0018,p0024,p0025,p0027,p0028,p0029,p0035,p0037,p0038,p0039,p0040,p0050]
    radiusSquared := 1/4
    witness := .segment 15 20
    originalFlag := false
    sourceNI := true
    journalLine := 27190
    identity := "17d2fd5fbb59b5e00871b1633f8c252ede15be296310acc07ebd02c1019cf09d" }
  checked := by decide +kernel

theorem w0126_check : PointSegmentLeaf.check w0126.data.points
    (Quadratic3.ofRat w0126.data.radiusSquared) w0126.data.witness = true := w0126.checked

def w0127 : CheckedWitness where
  data := {
    family := .q35
    factId := 174
    role := 3
    anchorId := 256
    pointIds := [256,47]
    points := [p0000,p0047]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 175
    identity := "5c6d3cdb05f90b69e6395027be3ce509ec5f876459f096a163d9e39be3bb0e82" }
  checked := by decide +kernel

theorem w0127_check : PointSegmentLeaf.check w0127.data.points
    (Quadratic3.ofRat w0127.data.radiusSquared) w0127.data.witness = true := w0127.checked

def w0128 : CheckedWitness where
  data := {
    family := .q35
    factId := 178
    role := 3
    anchorId := 256
    pointIds := [256,48]
    points := [p0000,p0048]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 179
    identity := "556f31aec0b5f184113574b1b998b55dc164125900f5602c58dc8010486c650d" }
  checked := by decide +kernel

theorem w0128_check : PointSegmentLeaf.check w0128.data.points
    (Quadratic3.ofRat w0128.data.radiusSquared) w0128.data.witness = true := w0128.checked

def w0129 : CheckedWitness where
  data := {
    family := .q35
    factId := 182
    role := 3
    anchorId := 256
    pointIds := [256,49]
    points := [p0000,p0049]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 183
    identity := "a8a28fdef205ae5272320eebebfbbf350f00994f32f73bac3b43645b78e47c38" }
  checked := by decide +kernel

theorem w0129_check : PointSegmentLeaf.check w0129.data.points
    (Quadratic3.ofRat w0129.data.radiusSquared) w0129.data.witness = true := w0129.checked

def w0130 : CheckedWitness where
  data := {
    family := .q35
    factId := 221
    role := 3
    anchorId := 256
    pointIds := [256,59]
    points := [p0000,p0059]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 222
    identity := "eed63c358988e019cabad20831fbd8e6917fcbb61d9fa10d518d2598b6f727e6" }
  checked := by decide +kernel

theorem w0130_check : PointSegmentLeaf.check w0130.data.points
    (Quadratic3.ofRat w0130.data.radiusSquared) w0130.data.witness = true := w0130.checked

def w0131 : CheckedWitness where
  data := {
    family := .q35
    factId := 225
    role := 3
    anchorId := 256
    pointIds := [256,60]
    points := [p0000,p0060]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 226
    identity := "61ccb6a1a7585f1ab080e427ba1f2beaeb9c6a6cbebb32297b6e6f50ed2a0480" }
  checked := by decide +kernel

theorem w0131_check : PointSegmentLeaf.check w0131.data.points
    (Quadratic3.ofRat w0131.data.radiusSquared) w0131.data.witness = true := w0131.checked

def w0132 : CheckedWitness where
  data := {
    family := .q35
    factId := 229
    role := 3
    anchorId := 256
    pointIds := [256,61]
    points := [p0000,p0061]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 230
    identity := "7d802a0b1d55f3bec31ee6c108e1cc982191af0ba6e5c3584ae6e79467ffffef" }
  checked := by decide +kernel

theorem w0132_check : PointSegmentLeaf.check w0132.data.points
    (Quadratic3.ofRat w0132.data.radiusSquared) w0132.data.witness = true := w0132.checked

def w0133 : CheckedWitness where
  data := {
    family := .q35
    factId := 232
    role := 3
    anchorId := 256
    pointIds := [256,62]
    points := [p0000,p0062]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 233
    identity := "e99823dda8a1a6584362885dbfb50f2498a7a45024087c01063bc6f51b777099" }
  checked := by decide +kernel

theorem w0133_check : PointSegmentLeaf.check w0133.data.points
    (Quadratic3.ofRat w0133.data.radiusSquared) w0133.data.witness = true := w0133.checked

def w0134 : CheckedWitness where
  data := {
    family := .q35
    factId := 236
    role := 3
    anchorId := 256
    pointIds := [256,63]
    points := [p0000,p0063]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 237
    identity := "01952fa196e5ca4c6a7e83b2b1aeb6f62637766ec119f4ab183f7a2cd77e57c7" }
  checked := by decide +kernel

theorem w0134_check : PointSegmentLeaf.check w0134.data.points
    (Quadratic3.ofRat w0134.data.radiusSquared) w0134.data.witness = true := w0134.checked

def w0135 : CheckedWitness where
  data := {
    family := .q35
    factId := 240
    role := 3
    anchorId := 256
    pointIds := [256,64]
    points := [p0000,p0064]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 241
    identity := "bd80f7ae2bb6542afd48ff6484e420b4e854cf747c0d98d4c5e5565708f2d2ce" }
  checked := by decide +kernel

theorem w0135_check : PointSegmentLeaf.check w0135.data.points
    (Quadratic3.ofRat w0135.data.radiusSquared) w0135.data.witness = true := w0135.checked

def w0136 : CheckedWitness where
  data := {
    family := .q35
    factId := 278
    role := 3
    anchorId := 256
    pointIds := [256,73]
    points := [p0000,p0073]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 279
    identity := "f6f36e533d96c5670451cf80c19d1efadfe9b65b89f1ee85e5549bd8fc61b447" }
  checked := by decide +kernel

theorem w0136_check : PointSegmentLeaf.check w0136.data.points
    (Quadratic3.ofRat w0136.data.radiusSquared) w0136.data.witness = true := w0136.checked

def w0137 : CheckedWitness where
  data := {
    family := .q35
    factId := 282
    role := 3
    anchorId := 256
    pointIds := [256,74]
    points := [p0000,p0074]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 283
    identity := "27b0c37a86a439878f5651db35c8a74f83d7fe71c0a51e8e07d59e65cf1c018a" }
  checked := by decide +kernel

theorem w0137_check : PointSegmentLeaf.check w0137.data.points
    (Quadratic3.ofRat w0137.data.radiusSquared) w0137.data.witness = true := w0137.checked

def w0138 : CheckedWitness where
  data := {
    family := .q35
    factId := 286
    role := 3
    anchorId := 256
    pointIds := [256,75]
    points := [p0000,p0075]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 287
    identity := "0066f6dd25ef4531bce4b39600ab0de26048ff4170716c3d0727386408f63d3f" }
  checked := by decide +kernel

theorem w0138_check : PointSegmentLeaf.check w0138.data.points
    (Quadratic3.ofRat w0138.data.radiusSquared) w0138.data.witness = true := w0138.checked

def w0139 : CheckedWitness where
  data := {
    family := .q35
    factId := 290
    role := 3
    anchorId := 256
    pointIds := [256,76]
    points := [p0000,p0076]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 291
    identity := "edd08db6d4d6f41e73f5de91d7b84ce12b25dfdb51f0d37a2fc8411e99590f87" }
  checked := by decide +kernel

theorem w0139_check : PointSegmentLeaf.check w0139.data.points
    (Quadratic3.ofRat w0139.data.radiusSquared) w0139.data.witness = true := w0139.checked

def w0140 : CheckedWitness where
  data := {
    family := .q35
    factId := 294
    role := 3
    anchorId := 256
    pointIds := [256,77]
    points := [p0000,p0077]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 295
    identity := "3d704f97887d086b8fbda8befa9bebccec41f2b6bb12929753eaed0d0b865f05" }
  checked := by decide +kernel

theorem w0140_check : PointSegmentLeaf.check w0140.data.points
    (Quadratic3.ofRat w0140.data.radiusSquared) w0140.data.witness = true := w0140.checked

def w0141 : CheckedWitness where
  data := {
    family := .q35
    factId := 298
    role := 3
    anchorId := 256
    pointIds := [256,78]
    points := [p0000,p0078]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 299
    identity := "0af1f178618408770104bd3a4a22673f25415167dfda31b2f7f3a2935ea2dcbc" }
  checked := by decide +kernel

theorem w0141_check : PointSegmentLeaf.check w0141.data.points
    (Quadratic3.ofRat w0141.data.radiusSquared) w0141.data.witness = true := w0141.checked

def w0142 : CheckedWitness where
  data := {
    family := .q35
    factId := 338
    role := 3
    anchorId := 256
    pointIds := [256,88]
    points := [p0000,p0088]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 339
    identity := "2d907e1e63c1a9fd17fd3b992500d4c85492d4527575844bd970edbd69ca6348" }
  checked := by decide +kernel

theorem w0142_check : PointSegmentLeaf.check w0142.data.points
    (Quadratic3.ofRat w0142.data.radiusSquared) w0142.data.witness = true := w0142.checked

def w0143 : CheckedWitness where
  data := {
    family := .q35
    factId := 339
    role := 5
    anchorId := 258
    pointIds := [258,88]
    points := [p0208,p0088]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 340
    identity := "438d748e18bf83a301544a94aac5c50827d0a770f8b3735d3509107e304a658b" }
  checked := by decide +kernel

theorem w0143_check : PointSegmentLeaf.check w0143.data.points
    (Quadratic3.ofRat w0143.data.radiusSquared) w0143.data.witness = true := w0143.checked

def w0144 : CheckedWitness where
  data := {
    family := .q35
    factId := 343
    role := 3
    anchorId := 256
    pointIds := [256,89]
    points := [p0000,p0089]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 344
    identity := "a56814ac14724041ceae025ca4445a8c67e624763c704c65170a783473e633a5" }
  checked := by decide +kernel

theorem w0144_check : PointSegmentLeaf.check w0144.data.points
    (Quadratic3.ofRat w0144.data.radiusSquared) w0144.data.witness = true := w0144.checked

def w0145 : CheckedWitness where
  data := {
    family := .q35
    factId := 344
    role := 5
    anchorId := 258
    pointIds := [258,89]
    points := [p0208,p0089]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 345
    identity := "1fb6c7b676069a4fe210f032c2748cb996ed96bef9844e2175b92935e16ce9c1" }
  checked := by decide +kernel

theorem w0145_check : PointSegmentLeaf.check w0145.data.points
    (Quadratic3.ofRat w0145.data.radiusSquared) w0145.data.witness = true := w0145.checked

def w0146 : CheckedWitness where
  data := {
    family := .q35
    factId := 348
    role := 3
    anchorId := 256
    pointIds := [256,90]
    points := [p0000,p0090]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 349
    identity := "da5a2c169dfd51aab0e9b1d2c851570ca5a227ff3aed5d9719800b2b640e1cd3" }
  checked := by decide +kernel

theorem w0146_check : PointSegmentLeaf.check w0146.data.points
    (Quadratic3.ofRat w0146.data.radiusSquared) w0146.data.witness = true := w0146.checked

def w0147 : CheckedWitness where
  data := {
    family := .q35
    factId := 352
    role := 3
    anchorId := 256
    pointIds := [256,91]
    points := [p0000,p0091]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 353
    identity := "4ad4ddf873f8bd0ec1cb56ff7bbdba41bf3f78268affc5a7d3278613b08c46bc" }
  checked := by decide +kernel

theorem w0147_check : PointSegmentLeaf.check w0147.data.points
    (Quadratic3.ofRat w0147.data.radiusSquared) w0147.data.witness = true := w0147.checked

def w0148 : CheckedWitness where
  data := {
    family := .q35
    factId := 355
    role := 3
    anchorId := 256
    pointIds := [256,92]
    points := [p0000,p0092]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 356
    identity := "034ee5f98829200f7eda56c3f7bd870642696f428ce129acd24daf3ad93f4646" }
  checked := by decide +kernel

theorem w0148_check : PointSegmentLeaf.check w0148.data.points
    (Quadratic3.ofRat w0148.data.radiusSquared) w0148.data.witness = true := w0148.checked

def w0149 : CheckedWitness where
  data := {
    family := .q35
    factId := 400
    role := 3
    anchorId := 256
    pointIds := [256,105]
    points := [p0000,p0105]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 401
    identity := "4104aba03d062fa2fc0ab5ac6b7e8a9f5043a5d9a294f32541f4b9a6315a4d1d" }
  checked := by decide +kernel

theorem w0149_check : PointSegmentLeaf.check w0149.data.points
    (Quadratic3.ofRat w0149.data.radiusSquared) w0149.data.witness = true := w0149.checked

def w0150 : CheckedWitness where
  data := {
    family := .q35
    factId := 401
    role := 5
    anchorId := 258
    pointIds := [258,105]
    points := [p0208,p0105]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 402
    identity := "f4f572041a30587534b081ede91ca0b898e252d9b949428041b5531b0f1f92b8" }
  checked := by decide +kernel

theorem w0150_check : PointSegmentLeaf.check w0150.data.points
    (Quadratic3.ofRat w0150.data.radiusSquared) w0150.data.witness = true := w0150.checked

def w0151 : CheckedWitness where
  data := {
    family := .q35
    factId := 405
    role := 3
    anchorId := 256
    pointIds := [256,106]
    points := [p0000,p0106]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 406
    identity := "bc3c296109efabcc1c1d37e5d4179a16358fad7a61aa5dd5bde5c0140ef35ff7" }
  checked := by decide +kernel

theorem w0151_check : PointSegmentLeaf.check w0151.data.points
    (Quadratic3.ofRat w0151.data.radiusSquared) w0151.data.witness = true := w0151.checked

def w0152 : CheckedWitness where
  data := {
    family := .q35
    factId := 406
    role := 5
    anchorId := 258
    pointIds := [258,106]
    points := [p0208,p0106]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 407
    identity := "6479a230010910bcabdeadd585166e09cbac22f0bee9c9a1a7ad73fb32b03749" }
  checked := by decide +kernel

theorem w0152_check : PointSegmentLeaf.check w0152.data.points
    (Quadratic3.ofRat w0152.data.radiusSquared) w0152.data.witness = true := w0152.checked

def w0153 : CheckedWitness where
  data := {
    family := .q35
    factId := 410
    role := 3
    anchorId := 256
    pointIds := [256,107]
    points := [p0000,p0107]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 411
    identity := "2b0fee7bf8cd4775144833bb7d35e01f3b42a84e4ca4b4b9d38bfd70dcfeef04" }
  checked := by decide +kernel

theorem w0153_check : PointSegmentLeaf.check w0153.data.points
    (Quadratic3.ofRat w0153.data.radiusSquared) w0153.data.witness = true := w0153.checked

def w0154 : CheckedWitness where
  data := {
    family := .q35
    factId := 411
    role := 5
    anchorId := 258
    pointIds := [258,107]
    points := [p0208,p0107]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 412
    identity := "923aef524db4968fd9eeef53bcb8b80219c45e782cba7fe6503d666ce59999cb" }
  checked := by decide +kernel

theorem w0154_check : PointSegmentLeaf.check w0154.data.points
    (Quadratic3.ofRat w0154.data.radiusSquared) w0154.data.witness = true := w0154.checked

def w0155 : CheckedWitness where
  data := {
    family := .q35
    factId := 412
    role := 3
    anchorId := 256
    pointIds := [256,108]
    points := [p0000,p0108]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 413
    identity := "1b669f1addd133745569e9e096087251acfba20e7e317fee4c22f3d0e03248f5" }
  checked := by decide +kernel

theorem w0155_check : PointSegmentLeaf.check w0155.data.points
    (Quadratic3.ofRat w0155.data.radiusSquared) w0155.data.witness = true := w0155.checked

def w0156 : CheckedWitness where
  data := {
    family := .q35
    factId := 413
    role := 5
    anchorId := 258
    pointIds := [258,108]
    points := [p0208,p0108]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 414
    identity := "d87e89d47baa0250fa71740f86fc68c9f30b97aece13f0b45d61be057013d049" }
  checked := by decide +kernel

theorem w0156_check : PointSegmentLeaf.check w0156.data.points
    (Quadratic3.ofRat w0156.data.radiusSquared) w0156.data.witness = true := w0156.checked

def w0157 : CheckedWitness where
  data := {
    family := .q35
    factId := 455
    role := 3
    anchorId := 256
    pointIds := [256,121]
    points := [p0000,p0121]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 456
    identity := "4494397a024ad357e6bb83603ded67af1aa41320a8cf32daec3aa9ebe4a202e1" }
  checked := by decide +kernel

theorem w0157_check : PointSegmentLeaf.check w0157.data.points
    (Quadratic3.ofRat w0157.data.radiusSquared) w0157.data.witness = true := w0157.checked

def w0158 : CheckedWitness where
  data := {
    family := .q35
    factId := 456
    role := 5
    anchorId := 258
    pointIds := [258,121]
    points := [p0208,p0121]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 457
    identity := "21c276c71810d308a7c55aec19487c09bb7948f28a91ce532649c255bae002b2" }
  checked := by decide +kernel

theorem w0158_check : PointSegmentLeaf.check w0158.data.points
    (Quadratic3.ofRat w0158.data.radiusSquared) w0158.data.witness = true := w0158.checked

def w0159 : CheckedWitness where
  data := {
    family := .q35
    factId := 460
    role := 3
    anchorId := 256
    pointIds := [256,122]
    points := [p0000,p0122]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 461
    identity := "19f7551747015b3cea0b37f770f4cd27f5c806e1ccf1b965ef7ae50939e7ab03" }
  checked := by decide +kernel

theorem w0159_check : PointSegmentLeaf.check w0159.data.points
    (Quadratic3.ofRat w0159.data.radiusSquared) w0159.data.witness = true := w0159.checked

def w0160 : CheckedWitness where
  data := {
    family := .q35
    factId := 461
    role := 5
    anchorId := 258
    pointIds := [258,122]
    points := [p0208,p0122]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 462
    identity := "de8c14a8b9402c8961133bf58f448c495220f05d76153b5076b2b92af5728d7f" }
  checked := by decide +kernel

theorem w0160_check : PointSegmentLeaf.check w0160.data.points
    (Quadratic3.ofRat w0160.data.radiusSquared) w0160.data.witness = true := w0160.checked

def w0161 : CheckedWitness where
  data := {
    family := .q35
    factId := 466
    role := 5
    anchorId := 258
    pointIds := [258,123]
    points := [p0208,p0123]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 467
    identity := "1f16f89cf03d3e9a8d653dd31e3a25f53603eac4a8f86d0df30b38e5091cd509" }
  checked := by decide +kernel

theorem w0161_check : PointSegmentLeaf.check w0161.data.points
    (Quadratic3.ofRat w0161.data.radiusSquared) w0161.data.witness = true := w0161.checked

def w0162 : CheckedWitness where
  data := {
    family := .q35
    factId := 470
    role := 5
    anchorId := 258
    pointIds := [258,124]
    points := [p0208,p0124]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 471
    identity := "7e04fca82d37c08a8545fd06773432389131d19db33bd17f103eb47dffe8d64f" }
  checked := by decide +kernel

theorem w0162_check : PointSegmentLeaf.check w0162.data.points
    (Quadratic3.ofRat w0162.data.radiusSquared) w0162.data.witness = true := w0162.checked

def w0163 : CheckedWitness where
  data := {
    family := .q35
    factId := 474
    role := 5
    anchorId := 258
    pointIds := [258,125]
    points := [p0208,p0125]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 475
    identity := "b8da7aa6f11eb49cbb744752a3a484a7433cb03df8edfd3b8d843164221febd6" }
  checked := by decide +kernel

theorem w0163_check : PointSegmentLeaf.check w0163.data.points
    (Quadratic3.ofRat w0163.data.radiusSquared) w0163.data.witness = true := w0163.checked

def w0164 : CheckedWitness where
  data := {
    family := .q35
    factId := 519
    role := 5
    anchorId := 258
    pointIds := [258,137]
    points := [p0208,p0137]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 520
    identity := "b91e8434bf7d5f1cd96a0015d561096d42309cfb506f08e713731648db1d94f1" }
  checked := by decide +kernel

theorem w0164_check : PointSegmentLeaf.check w0164.data.points
    (Quadratic3.ofRat w0164.data.radiusSquared) w0164.data.witness = true := w0164.checked

def w0165 : CheckedWitness where
  data := {
    family := .q35
    factId := 523
    role := 5
    anchorId := 258
    pointIds := [258,138]
    points := [p0208,p0138]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 524
    identity := "aec45a1b939bb7b2c607c6f99ad34b1e4983e92ee3887101825baabcc06fb216" }
  checked := by decide +kernel

theorem w0165_check : PointSegmentLeaf.check w0165.data.points
    (Quadratic3.ofRat w0165.data.radiusSquared) w0165.data.witness = true := w0165.checked

def w0166 : CheckedWitness where
  data := {
    family := .q35
    factId := 527
    role := 5
    anchorId := 258
    pointIds := [258,139]
    points := [p0208,p0139]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 528
    identity := "0257219f655d6ebbe15a3c15eb3cf93e37bf0fbb08c94c43ace0b5b448ff05eb" }
  checked := by decide +kernel

theorem w0166_check : PointSegmentLeaf.check w0166.data.points
    (Quadratic3.ofRat w0166.data.radiusSquared) w0166.data.witness = true := w0166.checked

def w0167 : CheckedWitness where
  data := {
    family := .q35
    factId := 532
    role := 5
    anchorId := 258
    pointIds := [258,140]
    points := [p0208,p0140]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 533
    identity := "662b202784ff75d68aa97f7f8926f8e6a81ce2f8be38218862f44c032dea3c09" }
  checked := by decide +kernel

theorem w0167_check : PointSegmentLeaf.check w0167.data.points
    (Quadratic3.ofRat w0167.data.radiusSquared) w0167.data.witness = true := w0167.checked

def w0168 : CheckedWitness where
  data := {
    family := .q35
    factId := 536
    role := 5
    anchorId := 258
    pointIds := [258,141]
    points := [p0208,p0141]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 537
    identity := "6e39b150b402d676f33d233cc3fa9a0e09108f7723d03fe00bdd9161ebd06919" }
  checked := by decide +kernel

theorem w0168_check : PointSegmentLeaf.check w0168.data.points
    (Quadratic3.ofRat w0168.data.radiusSquared) w0168.data.witness = true := w0168.checked

def w0169 : CheckedWitness where
  data := {
    family := .q35
    factId := 540
    role := 5
    anchorId := 258
    pointIds := [258,142]
    points := [p0208,p0142]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 541
    identity := "976f813d4cb618f846172e633dd07a613d4cfeae894efeab6c53f3deb137e321" }
  checked := by decide +kernel

theorem w0169_check : PointSegmentLeaf.check w0169.data.points
    (Quadratic3.ofRat w0169.data.radiusSquared) w0169.data.witness = true := w0169.checked

def w0170 : CheckedWitness where
  data := {
    family := .q35
    factId := 580
    role := 5
    anchorId := 258
    pointIds := [258,152]
    points := [p0208,p0152]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 581
    identity := "f1eec07f6620608f9b4d669f15e5844a19097d231171e014dfd9eaaec74febad" }
  checked := by decide +kernel

theorem w0170_check : PointSegmentLeaf.check w0170.data.points
    (Quadratic3.ofRat w0170.data.radiusSquared) w0170.data.witness = true := w0170.checked

def w0171 : CheckedWitness where
  data := {
    family := .q35
    factId := 584
    role := 5
    anchorId := 258
    pointIds := [258,153]
    points := [p0208,p0153]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 585
    identity := "2bd25185951ae014522b38a7e207cd603f769285815f9017ae619a47cf204645" }
  checked := by decide +kernel

theorem w0171_check : PointSegmentLeaf.check w0171.data.points
    (Quadratic3.ofRat w0171.data.radiusSquared) w0171.data.witness = true := w0171.checked

def w0172 : CheckedWitness where
  data := {
    family := .q35
    factId := 588
    role := 5
    anchorId := 258
    pointIds := [258,154]
    points := [p0208,p0154]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 589
    identity := "067d140897684a84731befd21298a304c8fdc7916cb9c9ff53fdbc59dc3dd4f4" }
  checked := by decide +kernel

theorem w0172_check : PointSegmentLeaf.check w0172.data.points
    (Quadratic3.ofRat w0172.data.radiusSquared) w0172.data.witness = true := w0172.checked

def w0173 : CheckedWitness where
  data := {
    family := .q35
    factId := 592
    role := 5
    anchorId := 258
    pointIds := [258,155]
    points := [p0208,p0155]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 593
    identity := "8284b06a969c473703d96993fe695d5ce912c59a3e232958914dffd649cedf89" }
  checked := by decide +kernel

theorem w0173_check : PointSegmentLeaf.check w0173.data.points
    (Quadratic3.ofRat w0173.data.radiusSquared) w0173.data.witness = true := w0173.checked

def w0174 : CheckedWitness where
  data := {
    family := .q35
    factId := 596
    role := 5
    anchorId := 258
    pointIds := [258,156]
    points := [p0208,p0156]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 597
    identity := "66fe60f039e7ed296a0152e08b5886ebb0490b99b86be093ff5dff93ee058f03" }
  checked := by decide +kernel

theorem w0174_check : PointSegmentLeaf.check w0174.data.points
    (Quadratic3.ofRat w0174.data.radiusSquared) w0174.data.witness = true := w0174.checked

def w0175 : CheckedWitness where
  data := {
    family := .q35
    factId := 600
    role := 5
    anchorId := 258
    pointIds := [258,157]
    points := [p0208,p0157]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 601
    identity := "d2699da2aa56ca0bf02f03c0e2bc5899f9e90d86c59d453d403b924b9600e4c8" }
  checked := by decide +kernel

theorem w0175_check : PointSegmentLeaf.check w0175.data.points
    (Quadratic3.ofRat w0175.data.radiusSquared) w0175.data.witness = true := w0175.checked

def w0176 : CheckedWitness where
  data := {
    family := .q35
    factId := 638
    role := 5
    anchorId := 258
    pointIds := [258,167]
    points := [p0208,p0167]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 639
    identity := "58d19997c7bf594eea2ddbd9f512615be7f3cec1baaf6b6635d5483cff991ee3" }
  checked := by decide +kernel

theorem w0176_check : PointSegmentLeaf.check w0176.data.points
    (Quadratic3.ofRat w0176.data.radiusSquared) w0176.data.witness = true := w0176.checked

def w0177 : CheckedWitness where
  data := {
    family := .q35
    factId := 643
    role := 5
    anchorId := 258
    pointIds := [258,168]
    points := [p0208,p0168]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 644
    identity := "a374ea9ec987a8b483501882e21a2cc26c03402ca7fad2e906d3a1a90a2ee64e" }
  checked := by decide +kernel

theorem w0177_check : PointSegmentLeaf.check w0177.data.points
    (Quadratic3.ofRat w0177.data.radiusSquared) w0177.data.witness = true := w0177.checked

def w0178 : CheckedWitness where
  data := {
    family := .q35
    factId := 647
    role := 5
    anchorId := 258
    pointIds := [258,169]
    points := [p0208,p0169]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 648
    identity := "9dd72f7d54b2a7176778d2daaa67005933e381730629ba5cb03d9f35f74cb1db" }
  checked := by decide +kernel

theorem w0178_check : PointSegmentLeaf.check w0178.data.points
    (Quadratic3.ofRat w0178.data.radiusSquared) w0178.data.witness = true := w0178.checked

def w0179 : CheckedWitness where
  data := {
    family := .q35
    factId := 823
    role := 5
    anchorId := 258
    pointIds := [258,217]
    points := [p0208,p0217]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 824
    identity := "c4b2b946fdadf9b0406c5095b13a82ef93927d304065eb5804fb68bf001e7c68" }
  checked := by decide +kernel

theorem w0179_check : PointSegmentLeaf.check w0179.data.points
    (Quadratic3.ofRat w0179.data.radiusSquared) w0179.data.witness = true := w0179.checked

def w0180 : CheckedWitness where
  data := {
    family := .q35
    factId := 827
    role := 5
    anchorId := 258
    pointIds := [258,218]
    points := [p0208,p0218]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 828
    identity := "c45138323ae6155247677074b1b73e99a33bf3ecb3d6edc545ee1528fd0d00d6" }
  checked := by decide +kernel

theorem w0180_check : PointSegmentLeaf.check w0180.data.points
    (Quadratic3.ofRat w0180.data.radiusSquared) w0180.data.witness = true := w0180.checked

def w0181 : CheckedWitness where
  data := {
    family := .q35
    factId := 857
    role := 3
    anchorId := 256
    pointIds := [256,227]
    points := [p0000,p0227]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 858
    identity := "34aa2cdce818acde48da5742cbd61c04c668bd7d2843cbdee8431f8e68e5fedf" }
  checked := by decide +kernel

theorem w0181_check : PointSegmentLeaf.check w0181.data.points
    (Quadratic3.ofRat w0181.data.radiusSquared) w0181.data.witness = true := w0181.checked

def w0182 : CheckedWitness where
  data := {
    family := .q35
    factId := 861
    role := 3
    anchorId := 256
    pointIds := [256,228]
    points := [p0000,p0228]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 862
    identity := "9736f16ad2ed6f22bee4a356cb7ba0968973c9493307cde71cf4017ec725b184" }
  checked := by decide +kernel

theorem w0182_check : PointSegmentLeaf.check w0182.data.points
    (Quadratic3.ofRat w0182.data.radiusSquared) w0182.data.witness = true := w0182.checked

def w0183 : CheckedWitness where
  data := {
    family := .q35
    factId := 865
    role := 3
    anchorId := 256
    pointIds := [256,229]
    points := [p0000,p0229]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 866
    identity := "0ccaaf799e55fc1c816a627839a6c16e4269366a03be33fa2273a4f1dcf1b7b0" }
  checked := by decide +kernel

theorem w0183_check : PointSegmentLeaf.check w0183.data.points
    (Quadratic3.ofRat w0183.data.radiusSquared) w0183.data.witness = true := w0183.checked

def w0184 : CheckedWitness where
  data := {
    family := .q35
    factId := 869
    role := 3
    anchorId := 256
    pointIds := [256,230]
    points := [p0000,p0230]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 870
    identity := "55760c7f9076fa02363d2d6a7af6d0aa03450b25872e403dc65a44243abc58c3" }
  checked := by decide +kernel

theorem w0184_check : PointSegmentLeaf.check w0184.data.points
    (Quadratic3.ofRat w0184.data.radiusSquared) w0184.data.witness = true := w0184.checked

def w0185 : CheckedWitness where
  data := {
    family := .q35
    factId := 874
    role := 3
    anchorId := 256
    pointIds := [256,231]
    points := [p0000,p0231]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 875
    identity := "a99f01fb2fa8a918f74befeb856827486bd6362d4109244893632251b2edee5d" }
  checked := by decide +kernel

theorem w0185_check : PointSegmentLeaf.check w0185.data.points
    (Quadratic3.ofRat w0185.data.radiusSquared) w0185.data.witness = true := w0185.checked

def w0186 : CheckedWitness where
  data := {
    family := .q35
    factId := 879
    role := 3
    anchorId := 256
    pointIds := [256,232]
    points := [p0000,p0232]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 880
    identity := "792d1df3f73be8019b28c3ec252f4580b8c647839a7ca8715c6fda10e9df16ca" }
  checked := by decide +kernel

theorem w0186_check : PointSegmentLeaf.check w0186.data.points
    (Quadratic3.ofRat w0186.data.radiusSquared) w0186.data.witness = true := w0186.checked

def w0187 : CheckedWitness where
  data := {
    family := .q35
    factId := 884
    role := 3
    anchorId := 256
    pointIds := [256,233]
    points := [p0000,p0233]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 885
    identity := "293171700b87850eb1d51f6b49ef703079205082e95782d74771e9fa7ebca1b6" }
  checked := by decide +kernel

theorem w0187_check : PointSegmentLeaf.check w0187.data.points
    (Quadratic3.ofRat w0187.data.radiusSquared) w0187.data.witness = true := w0187.checked

def w0188 : CheckedWitness where
  data := {
    family := .q35
    factId := 888
    role := 3
    anchorId := 256
    pointIds := [256,234]
    points := [p0000,p0234]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 889
    identity := "3bb1ca1fd5bb169e0dc5037f69681ca5e1e51228f363b39956b1688cfcb40d5e" }
  checked := by decide +kernel

theorem w0188_check : PointSegmentLeaf.check w0188.data.points
    (Quadratic3.ofRat w0188.data.radiusSquared) w0188.data.witness = true := w0188.checked

def w0189 : CheckedWitness where
  data := {
    family := .q35
    factId := 892
    role := 3
    anchorId := 256
    pointIds := [256,235]
    points := [p0000,p0235]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 893
    identity := "094f0a85ac00ac31551880c1da352ca491b5a0fdec4cb9de82d67e4c6601fc43" }
  checked := by decide +kernel

theorem w0189_check : PointSegmentLeaf.check w0189.data.points
    (Quadratic3.ofRat w0189.data.radiusSquared) w0189.data.witness = true := w0189.checked

def w0190 : CheckedWitness where
  data := {
    family := .q35
    factId := 896
    role := 3
    anchorId := 256
    pointIds := [256,236]
    points := [p0000,p0236]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 897
    identity := "96361e9a288c270b6bbaa44fbec67b0493fd836ee96f714637d346d05a41ccb5" }
  checked := by decide +kernel

theorem w0190_check : PointSegmentLeaf.check w0190.data.points
    (Quadratic3.ofRat w0190.data.radiusSquared) w0190.data.witness = true := w0190.checked

def w0191 : CheckedWitness where
  data := {
    family := .q35
    factId := 901
    role := 3
    anchorId := 256
    pointIds := [256,237]
    points := [p0000,p0237]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 902
    identity := "4e2a2dbcda11a1f728140e9ac26dfa68adee99234fb2474270597fa7f81d5f3c" }
  checked := by decide +kernel

theorem w0191_check : PointSegmentLeaf.check w0191.data.points
    (Quadratic3.ofRat w0191.data.radiusSquared) w0191.data.witness = true := w0191.checked

def w0192 : CheckedWitness where
  data := {
    family := .q35
    factId := 906
    role := 3
    anchorId := 256
    pointIds := [256,238]
    points := [p0000,p0238]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 907
    identity := "a52589a47b8ffff6aae2b95d14e1640622675f78f090e6a246a45603c49bb169" }
  checked := by decide +kernel

theorem w0192_check : PointSegmentLeaf.check w0192.data.points
    (Quadratic3.ofRat w0192.data.radiusSquared) w0192.data.witness = true := w0192.checked

def w0193 : CheckedWitness where
  data := {
    family := .q35
    factId := 911
    role := 3
    anchorId := 256
    pointIds := [256,239]
    points := [p0000,p0239]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 912
    identity := "648c3b18956a976901d4a5e3d748d48e3e453ee382667e0ebb4fc92f91e7b7af" }
  checked := by decide +kernel

theorem w0193_check : PointSegmentLeaf.check w0193.data.points
    (Quadratic3.ofRat w0193.data.radiusSquared) w0193.data.witness = true := w0193.checked

def w0194 : CheckedWitness where
  data := {
    family := .q35
    factId := 912
    role := 5
    anchorId := 258
    pointIds := [258,239]
    points := [p0208,p0239]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 913
    identity := "0b616d21db9066186c672183215135452efc4e16d284f089a04c292c3cf20865" }
  checked := by decide +kernel

theorem w0194_check : PointSegmentLeaf.check w0194.data.points
    (Quadratic3.ofRat w0194.data.radiusSquared) w0194.data.witness = true := w0194.checked

def w0195 : CheckedWitness where
  data := {
    family := .q35
    factId := 916
    role := 3
    anchorId := 256
    pointIds := [256,240]
    points := [p0000,p0240]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 917
    identity := "defa08fcb4825d063dc19b8a738b1e25d1126feb13b5df8b3e6ae293d4ffa664" }
  checked := by decide +kernel

theorem w0195_check : PointSegmentLeaf.check w0195.data.points
    (Quadratic3.ofRat w0195.data.radiusSquared) w0195.data.witness = true := w0195.checked

def w0196 : CheckedWitness where
  data := {
    family := .q35
    factId := 917
    role := 5
    anchorId := 258
    pointIds := [258,240]
    points := [p0208,p0240]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 918
    identity := "9a915e3a1c5f6a34d18bde80a6ab5174cc619ecc4da69d40f103f9d0ead8d373" }
  checked := by decide +kernel

theorem w0196_check : PointSegmentLeaf.check w0196.data.points
    (Quadratic3.ofRat w0196.data.radiusSquared) w0196.data.witness = true := w0196.checked

def w0197 : CheckedWitness where
  data := {
    family := .q35
    factId := 921
    role := 3
    anchorId := 256
    pointIds := [256,241]
    points := [p0000,p0241]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 922
    identity := "0fa1143aac475030a2bbffdec1c7ac34521cdfca7205d2eb3c33f24ce49d2633" }
  checked := by decide +kernel

theorem w0197_check : PointSegmentLeaf.check w0197.data.points
    (Quadratic3.ofRat w0197.data.radiusSquared) w0197.data.witness = true := w0197.checked

def w0198 : CheckedWitness where
  data := {
    family := .q35
    factId := 922
    role := 5
    anchorId := 258
    pointIds := [258,241]
    points := [p0208,p0241]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 923
    identity := "a7d7cef522db36adfd1a17d05e206f1ddef8e1034f9ba1dd776805d66b6bdfcb" }
  checked := by decide +kernel

theorem w0198_check : PointSegmentLeaf.check w0198.data.points
    (Quadratic3.ofRat w0198.data.radiusSquared) w0198.data.witness = true := w0198.checked

def w0199 : CheckedWitness where
  data := {
    family := .q35
    factId := 926
    role := 3
    anchorId := 256
    pointIds := [256,242]
    points := [p0000,p0242]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 927
    identity := "f391de22481d4c12be295324ded76a57992a3fde45f52f972eabf196dbe00933" }
  checked := by decide +kernel

theorem w0199_check : PointSegmentLeaf.check w0199.data.points
    (Quadratic3.ofRat w0199.data.radiusSquared) w0199.data.witness = true := w0199.checked

def w0200 : CheckedWitness where
  data := {
    family := .q35
    factId := 927
    role := 5
    anchorId := 258
    pointIds := [258,242]
    points := [p0208,p0242]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 928
    identity := "701e5341b801ff601d02aa85c11dc7a74ab62d5cf5d2b0ed18d5a56bcffbc6c4" }
  checked := by decide +kernel

theorem w0200_check : PointSegmentLeaf.check w0200.data.points
    (Quadratic3.ofRat w0200.data.radiusSquared) w0200.data.witness = true := w0200.checked

def w0201 : CheckedWitness where
  data := {
    family := .q35
    factId := 932
    role := 5
    anchorId := 258
    pointIds := [258,243]
    points := [p0208,p0243]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 933
    identity := "00f1a019bb2c80fae7c55f4257169409be2e0512cbfb3bf3f6b981ccce0e3559" }
  checked := by decide +kernel

theorem w0201_check : PointSegmentLeaf.check w0201.data.points
    (Quadratic3.ofRat w0201.data.radiusSquared) w0201.data.witness = true := w0201.checked

def w0202 : CheckedWitness where
  data := {
    family := .q35
    factId := 937
    role := 5
    anchorId := 258
    pointIds := [258,244]
    points := [p0208,p0244]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 938
    identity := "a794b955ebacd52b47b9054c77f03708221be0ced8f24bdca6b5b0f8df860614" }
  checked := by decide +kernel

theorem w0202_check : PointSegmentLeaf.check w0202.data.points
    (Quadratic3.ofRat w0202.data.radiusSquared) w0202.data.witness = true := w0202.checked

def w0203 : CheckedWitness where
  data := {
    family := .q35
    factId := 941
    role := 5
    anchorId := 258
    pointIds := [258,245]
    points := [p0208,p0245]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 942
    identity := "b68f371ece9e57400446fed13b7f9a81ff709f89d46bb8ed3a771f5d7d05261f" }
  checked := by decide +kernel

theorem w0203_check : PointSegmentLeaf.check w0203.data.points
    (Quadratic3.ofRat w0203.data.radiusSquared) w0203.data.witness = true := w0203.checked

def w0204 : CheckedWitness where
  data := {
    family := .q35
    factId := 945
    role := 5
    anchorId := 258
    pointIds := [258,246]
    points := [p0208,p0246]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 946
    identity := "26f1d187e0d2be5087d807ec77b8b1012e5d40944824da31945c7f09024d0816" }
  checked := by decide +kernel

theorem w0204_check : PointSegmentLeaf.check w0204.data.points
    (Quadratic3.ofRat w0204.data.radiusSquared) w0204.data.witness = true := w0204.checked

def w0205 : CheckedWitness where
  data := {
    family := .q35
    factId := 949
    role := 5
    anchorId := 258
    pointIds := [258,247]
    points := [p0208,p0247]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 950
    identity := "99ca4429e14566f0ac225fb20026481808ef8264d990d3e0ca3949ca8a523562" }
  checked := by decide +kernel

theorem w0205_check : PointSegmentLeaf.check w0205.data.points
    (Quadratic3.ofRat w0205.data.radiusSquared) w0205.data.witness = true := w0205.checked

def w0206 : CheckedWitness where
  data := {
    family := .q35
    factId := 953
    role := 5
    anchorId := 258
    pointIds := [258,248]
    points := [p0208,p0248]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 954
    identity := "c0627f6c2d0b47b008892c3a14348ca5222898c182fe2479927e9b46b661e8e8" }
  checked := by decide +kernel

theorem w0206_check : PointSegmentLeaf.check w0206.data.points
    (Quadratic3.ofRat w0206.data.radiusSquared) w0206.data.witness = true := w0206.checked

def w0207 : CheckedWitness where
  data := {
    family := .q35
    factId := 958
    role := 5
    anchorId := 258
    pointIds := [258,249]
    points := [p0208,p0249]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 959
    identity := "bd69e6cfc983c229d053ac36dc64b84470ebaee62bd4673065c4186c83c53ce3" }
  checked := by decide +kernel

theorem w0207_check : PointSegmentLeaf.check w0207.data.points
    (Quadratic3.ofRat w0207.data.radiusSquared) w0207.data.witness = true := w0207.checked

def w0208 : CheckedWitness where
  data := {
    family := .q35
    factId := 963
    role := 5
    anchorId := 258
    pointIds := [258,250]
    points := [p0208,p0250]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 964
    identity := "9f09107bdae639bedc0345795f346098ad706ea9625a401f50a5ab1af2cef34d" }
  checked := by decide +kernel

theorem w0208_check : PointSegmentLeaf.check w0208.data.points
    (Quadratic3.ofRat w0208.data.radiusSquared) w0208.data.witness = true := w0208.checked

def w0209 : CheckedWitness where
  data := {
    family := .q35
    factId := 967
    role := 5
    anchorId := 258
    pointIds := [258,251]
    points := [p0208,p0251]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 968
    identity := "b9e78ae55383861660900a32920feddccac816c152cf6f7174540c76e48bba15" }
  checked := by decide +kernel

theorem w0209_check : PointSegmentLeaf.check w0209.data.points
    (Quadratic3.ofRat w0209.data.radiusSquared) w0209.data.witness = true := w0209.checked

def w0210 : CheckedWitness where
  data := {
    family := .q35
    factId := 971
    role := 5
    anchorId := 258
    pointIds := [258,252]
    points := [p0208,p0252]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 972
    identity := "1c5e8039fd33a25aa302830c1057c3cccb763b72687e810afeea928a5639bb0b" }
  checked := by decide +kernel

theorem w0210_check : PointSegmentLeaf.check w0210.data.points
    (Quadratic3.ofRat w0210.data.radiusSquared) w0210.data.witness = true := w0210.checked

def w0211 : CheckedWitness where
  data := {
    family := .q35
    factId := 1012
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198]
    points := [p0208,p0170,p0187,p0198]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 1013
    identity := "e9812d7ba757d3f34a7a987a3d4aab35400ace90b6449c9f21716edb85cc0ce2" }
  checked := by decide +kernel

theorem w0211_check : PointSegmentLeaf.check w0211.data.points
    (Quadratic3.ofRat w0211.data.radiusSquared) w0211.data.witness = true := w0211.checked

def w0212 : CheckedWitness where
  data := {
    family := .q35
    factId := 1139
    role := 3
    anchorId := 256
    pointIds := [256,9,19,50]
    points := [p0000,p0009,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 1140
    identity := "52cee27f8b12136426477d11db7a0ad85adce68ec40bc8f2c2f362323a23f2b8" }
  checked := by decide +kernel

theorem w0212_check : PointSegmentLeaf.check w0212.data.points
    (Quadratic3.ofRat w0212.data.radiusSquared) w0212.data.witness = true := w0212.checked

def w0213 : CheckedWitness where
  data := {
    family := .q35
    factId := 1239
    role := 3
    anchorId := 256
    pointIds := [256,0,9,19,50]
    points := [p0000,p0000,p0009,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 2 4
    originalFlag := false
    sourceNI := true
    journalLine := 1240
    identity := "51daa077a4350242a28a63cf118fd25c4e3461ade502d2f7f90a72af13ffd555" }
  checked := by decide +kernel

theorem w0213_check : PointSegmentLeaf.check w0213.data.points
    (Quadratic3.ofRat w0213.data.radiusSquared) w0213.data.witness = true := w0213.checked

def w0214 : CheckedWitness where
  data := {
    family := .q35
    factId := 1503
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,19,50]
    points := [p0000,p0000,p0001,p0009,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 3 5
    originalFlag := false
    sourceNI := true
    journalLine := 1504
    identity := "560dfbc936fd9d81121a8c24a6e6fc622caf055e77c431667a82571668c437ea" }
  checked := by decide +kernel

theorem w0214_check : PointSegmentLeaf.check w0214.data.points
    (Quadratic3.ofRat w0214.data.radiusSquared) w0214.data.witness = true := w0214.checked

def w0215 : CheckedWitness where
  data := {
    family := .q35
    factId := 1709
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,10,19,50]
    points := [p0000,p0000,p0001,p0009,p0010,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 3 6
    originalFlag := false
    sourceNI := true
    journalLine := 1710
    identity := "20764869c5c26d2d6d3d72bef942537cbe3ba556ae54321a86d0f0198373f645" }
  checked := by decide +kernel

theorem w0215_check : PointSegmentLeaf.check w0215.data.points
    (Quadratic3.ofRat w0215.data.radiusSquared) w0215.data.witness = true := w0215.checked

def w0216 : CheckedWitness where
  data := {
    family := .q35
    factId := 1839
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,19,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 4 6
    originalFlag := false
    sourceNI := true
    journalLine := 1840
    identity := "51e353911c32b22f4b85c24885d18ca03da14aab339c8723e48bcbb860c5dff7" }
  checked := by decide +kernel

theorem w0216_check : PointSegmentLeaf.check w0216.data.points
    (Quadratic3.ofRat w0216.data.radiusSquared) w0216.data.witness = true := w0216.checked

def w0217 : CheckedWitness where
  data := {
    family := .q35
    factId := 2718
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,19,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 4 7
    originalFlag := false
    sourceNI := true
    journalLine := 2719
    identity := "87194ba88fe806889b5218b26c00f34d1384fe9a50330656f19f45aef612d663" }
  checked := by decide +kernel

theorem w0217_check : PointSegmentLeaf.check w0217.data.points
    (Quadratic3.ofRat w0217.data.radiusSquared) w0217.data.witness = true := w0217.checked

def w0218 : CheckedWitness where
  data := {
    family := .q35
    factId := 3155
    role := 3
    anchorId := 256
    pointIds := [256,0,9,10,19,50]
    points := [p0000,p0000,p0009,p0010,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 3156
    identity := "440f73a3164e2ab0fe154f65db43cdbefd7fcc387fc990b22c5ccf65c7d2bfe6" }
  checked := by decide +kernel

theorem w0218_check : PointSegmentLeaf.check w0218.data.points
    (Quadratic3.ofRat w0218.data.radiusSquared) w0218.data.witness = true := w0218.checked

def w0219 : CheckedWitness where
  data := {
    family := .q35
    factId := 3845
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,20,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 4 7
    originalFlag := false
    sourceNI := true
    journalLine := 3846
    identity := "bd1a3ecc9375f14459b251d929b2b50cde62e5708f0bdd6e08e8d41e3005db55" }
  checked := by decide +kernel

theorem w0219_check : PointSegmentLeaf.check w0219.data.points
    (Quadratic3.ofRat w0219.data.radiusSquared) w0219.data.witness = true := w0219.checked

def w0220 : CheckedWitness where
  data := {
    family := .q35
    factId := 4814
    role := 3
    anchorId := 256
    pointIds := [256,0,9,10,19,21,50]
    points := [p0000,p0000,p0009,p0010,p0019,p0021,p0050]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 4815
    identity := "4d638dc7ba7da9178b0c1f0b500840212bce6cceb1a669622c4906f7cfbedc87" }
  checked := by decide +kernel

theorem w0220_check : PointSegmentLeaf.check w0220.data.points
    (Quadratic3.ofRat w0220.data.radiusSquared) w0220.data.witness = true := w0220.checked

def w0221 : CheckedWitness where
  data := {
    family := .q35
    factId := 5036
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,10,19,21,50]
    points := [p0000,p0000,p0001,p0009,p0010,p0019,p0021,p0050]
    radiusSquared := 1/4
    witness := .segment 3 7
    originalFlag := false
    sourceNI := true
    journalLine := 5037
    identity := "7e3570b8874704e2b7a48c6656a69214b8185f40820e48f90e883c15a538943b" }
  checked := by decide +kernel

theorem w0221_check : PointSegmentLeaf.check w0221.data.points
    (Quadratic3.ofRat w0221.data.radiusSquared) w0221.data.witness = true := w0221.checked

def w0222 : CheckedWitness where
  data := {
    family := .q35
    factId := 5292
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198,199,200,208,209,210]
    points := [p0208,p0170,p0187,p0198,p0199,p0200,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 5293
    identity := "83b959d5b30dbff2929be7816cef05251900a29ab1c2ba616a5b52f731c5affc" }
  checked := by decide +kernel

theorem w0222_check : PointSegmentLeaf.check w0222.data.points
    (Quadratic3.ofRat w0222.data.radiusSquared) w0222.data.witness = true := w0222.checked

def w0223 : CheckedWitness where
  data := {
    family := .q35
    factId := 7849
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,12,21,22,33,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0012,p0021,p0022,p0033,p0050]
    radiusSquared := 1/4
    witness := .segment 5 12
    originalFlag := false
    sourceNI := true
    journalLine := 7850
    identity := "d13adb6643034b4219c8d407deb7fc6cdc68be6664937c3b93a833e7e6eb1e3f" }
  checked := by decide +kernel

theorem w0223_check : PointSegmentLeaf.check w0223.data.points
    (Quadratic3.ofRat w0223.data.radiusSquared) w0223.data.witness = true := w0223.checked

def w0224 : CheckedWitness where
  data := {
    family := .q35
    factId := 7875
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,11,21,33,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0011,p0021,p0033,p0050]
    radiusSquared := 1/4
    witness := .segment 4 9
    originalFlag := false
    sourceNI := true
    journalLine := 7876
    identity := "48972e2eedd3df2eb17d7baf90036f56363b0e3d0a0b622244e53688749b9658" }
  checked := by decide +kernel

theorem w0224_check : PointSegmentLeaf.check w0224.data.points
    (Quadratic3.ofRat w0224.data.radiusSquared) w0224.data.witness = true := w0224.checked

def w0225 : CheckedWitness where
  data := {
    family := .q35
    factId := 8611
    role := 3
    anchorId := 256
    pointIds := [256,9,20,50]
    points := [p0000,p0009,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 8612
    identity := "6f18deeb25336be3f5a78700b6c701a4953a419bc857ae82e2d6047aee778c34" }
  checked := by decide +kernel

theorem w0225_check : PointSegmentLeaf.check w0225.data.points
    (Quadratic3.ofRat w0225.data.radiusSquared) w0225.data.witness = true := w0225.checked

def w0226 : CheckedWitness where
  data := {
    family := .q35
    factId := 9163
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,11,19,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0011,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 4 8
    originalFlag := false
    sourceNI := true
    journalLine := 9164
    identity := "789da4f019628a7d083e6c9149bd9fe26759b9fc2092145261c8bddaf778d6ee" }
  checked := by decide +kernel

theorem w0226_check : PointSegmentLeaf.check w0226.data.points
    (Quadratic3.ofRat w0226.data.radiusSquared) w0226.data.witness = true := w0226.checked

def w0227 : CheckedWitness where
  data := {
    family := .q35
    factId := 9366
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,20,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 5 8
    originalFlag := false
    sourceNI := true
    journalLine := 9367
    identity := "9116a0621e23712ae95305aebf6065fb380fa073643c8448bd5076a02e70e49f" }
  checked := by decide +kernel

theorem w0227_check : PointSegmentLeaf.check w0227.data.points
    (Quadratic3.ofRat w0227.data.radiusSquared) w0227.data.witness = true := w0227.checked

def w0228 : CheckedWitness where
  data := {
    family := .q35
    factId := 9771
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,12,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0012,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 5 10
    originalFlag := false
    sourceNI := true
    journalLine := 9772
    identity := "1fb534a9ca64d9717c75e0c6717e608be74dfdf70f36e258673be14a43be0375" }
  checked := by decide +kernel

theorem w0228_check : PointSegmentLeaf.check w0228.data.points
    (Quadratic3.ofRat w0228.data.radiusSquared) w0228.data.witness = true := w0228.checked

def w0229 : CheckedWitness where
  data := {
    family := .q35
    factId := 9824
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 5 8
    originalFlag := false
    sourceNI := true
    journalLine := 9825
    identity := "bcaf32a3cf5e1118bb268c8e480f1f83753024028958f380bf3526d4189ceb89" }
  checked := by decide +kernel

theorem w0229_check : PointSegmentLeaf.check w0229.data.points
    (Quadratic3.ofRat w0229.data.radiusSquared) w0229.data.witness = true := w0229.checked

def w0230 : CheckedWitness where
  data := {
    family := .q35
    factId := 9983
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,12,20,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0012,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 5 10
    originalFlag := false
    sourceNI := true
    journalLine := 9984
    identity := "2fe8281f4fdb4e5fff6ddc1795658921c1bedd36ddbf42dfacf58e308f192783" }
  checked := by decide +kernel

theorem w0230_check : PointSegmentLeaf.check w0230.data.points
    (Quadratic3.ofRat w0230.data.radiusSquared) w0230.data.witness = true := w0230.checked

def w0231 : CheckedWitness where
  data := {
    family := .q35
    factId := 10123
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,11,20,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0011,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 4 8
    originalFlag := false
    sourceNI := true
    journalLine := 10124
    identity := "6712b3b308a2a26584174ac5310edfb2eb3b265b95e41dce7684e8fff2a498fc" }
  checked := by decide +kernel

theorem w0231_check : PointSegmentLeaf.check w0231.data.points
    (Quadratic3.ofRat w0231.data.radiusSquared) w0231.data.witness = true := w0231.checked

def w0232 : CheckedWitness where
  data := {
    family := .q35
    factId := 12332
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,20,50]
    points := [p0000,p0000,p0001,p0009,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 3 5
    originalFlag := false
    sourceNI := true
    journalLine := 12333
    identity := "bc6cc81bcf6088e89a25498a53219f6518898d5445d7d7050a4c3ba4abdf522b" }
  checked := by decide +kernel

theorem w0232_check : PointSegmentLeaf.check w0232.data.points
    (Quadratic3.ofRat w0232.data.radiusSquared) w0232.data.witness = true := w0232.checked

def w0233 : CheckedWitness where
  data := {
    family := .q35
    factId := 13363
    role := 5
    anchorId := 258
    pointIds := [258,170,188,198,199,208,209]
    points := [p0208,p0170,p0188,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 13364
    identity := "62610d641d867fd4fbd993dcc6e36e7bf82bb024f0ccd0d9d27915e80556b248" }
  checked := by decide +kernel

theorem w0233_check : PointSegmentLeaf.check w0233.data.points
    (Quadratic3.ofRat w0233.data.radiusSquared) w0233.data.witness = true := w0233.checked

def w0234 : CheckedWitness where
  data := {
    family := .q35
    factId := 13431
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,19,21,30,32,33,37,46]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0019,p0021,p0030,p0032,p0033,p0037,p0046]
    radiusSquared := 1/4
    witness := .segment 11 12
    originalFlag := false
    sourceNI := true
    journalLine := 13432
    identity := "58b4d3096815e2597409cda7a63c6bf326bafd97418632e081de89a5e1780e63" }
  checked := by decide +kernel

theorem w0234_check : PointSegmentLeaf.check w0234.data.points
    (Quadratic3.ofRat w0234.data.radiusSquared) w0234.data.witness = true := w0234.checked

def w0235 : CheckedWitness where
  data := {
    family := .q35
    factId := 13740
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,11,12,19,22,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0011,p0012,p0019,p0022,p0050]
    radiusSquared := 1/4
    witness := .segment 5 10
    originalFlag := false
    sourceNI := true
    journalLine := 13741
    identity := "f8151d67ddda9fff4010da6d72d316d0d37612237ba9ce967b3017564d881308" }
  checked := by decide +kernel

theorem w0235_check : PointSegmentLeaf.check w0235.data.points
    (Quadratic3.ofRat w0235.data.radiusSquared) w0235.data.witness = true := w0235.checked

def w0236 : CheckedWitness where
  data := {
    family := .q35
    factId := 13819
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,10,21,33,38,45]
    points := [p0000,p0000,p0001,p0009,p0010,p0021,p0033,p0038,p0045]
    radiusSquared := 1/4
    witness := .segment 7 8
    originalFlag := false
    sourceNI := true
    journalLine := 13820
    identity := "22e2427ff20fbca0de18773a640b9691ae4520b27c3c9d922d215b6cf680cf08" }
  checked := by decide +kernel

theorem w0236_check : PointSegmentLeaf.check w0236.data.points
    (Quadratic3.ofRat w0236.data.radiusSquared) w0236.data.witness = true := w0236.checked

def w0237 : CheckedWitness where
  data := {
    family := .q35
    factId := 15399
    role := 3
    anchorId := 256
    pointIds := [256,0,9,20,50]
    points := [p0000,p0000,p0009,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 2 4
    originalFlag := false
    sourceNI := true
    journalLine := 15400
    identity := "ef26be244ac4f6af4fc5a78b974cbdd7177042a68b5685310aced05d138cfef4" }
  checked := by decide +kernel

theorem w0237_check : PointSegmentLeaf.check w0237.data.points
    (Quadratic3.ofRat w0237.data.radiusSquared) w0237.data.witness = true := w0237.checked

def w0238 : CheckedWitness where
  data := {
    family := .q35
    factId := 15438
    role := 5
    anchorId := 258
    pointIds := [258,170,178,198,199,208,209,210]
    points := [p0208,p0170,p0178,p0198,p0199,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 15439
    identity := "310f5610884744e092c71bf27aafca7c95496b618a87bf21465bd6f971fc153d" }
  checked := by decide +kernel

theorem w0238_check : PointSegmentLeaf.check w0238.data.points
    (Quadratic3.ofRat w0238.data.radiusSquared) w0238.data.witness = true := w0238.checked

def w0239 : CheckedWitness where
  data := {
    family := .q35
    factId := 15471
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198,199,208,209,210]
    points := [p0208,p0170,p0187,p0198,p0199,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 15472
    identity := "f4cf4c6fda5617d8ad304df1598d846cde1fb494e82550261f2adbb888fbdbc7" }
  checked := by decide +kernel

theorem w0239_check : PointSegmentLeaf.check w0239.data.points
    (Quadratic3.ofRat w0239.data.radiusSquared) w0239.data.witness = true := w0239.checked

def w0240 : CheckedWitness where
  data := {
    family := .q35
    factId := 15482
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,10,20,50]
    points := [p0000,p0000,p0001,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 3 6
    originalFlag := false
    sourceNI := true
    journalLine := 15483
    identity := "a8a0e130678ba135e163b7ebdf1cee7584f59ad7f2c237a74ee6b6fac2625bba" }
  checked := by decide +kernel

theorem w0240_check : PointSegmentLeaf.check w0240.data.points
    (Quadratic3.ofRat w0240.data.radiusSquared) w0240.data.witness = true := w0240.checked

def w0241 : CheckedWitness where
  data := {
    family := .q35
    factId := 16916
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,10,11,20,50]
    points := [p0000,p0000,p0001,p0009,p0010,p0011,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 3 7
    originalFlag := false
    sourceNI := true
    journalLine := 16917
    identity := "4ba28e6af9b7e61bd8c3f9853d2ab4fb0cf35436cafa6518e107dda2417334f0" }
  checked := by decide +kernel

theorem w0241_check : PointSegmentLeaf.check w0241.data.points
    (Quadratic3.ofRat w0241.data.radiusSquared) w0241.data.witness = true := w0241.checked

def w0242 : CheckedWitness where
  data := {
    family := .q35
    factId := 16988
    role := 3
    anchorId := 256
    pointIds := [256,0,1,5,9,10,20,50]
    points := [p0000,p0000,p0001,p0005,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 4 7
    originalFlag := false
    sourceNI := true
    journalLine := 16989
    identity := "769223ff4deaccd34217e3732dcce8ba0ad0e568cd82351b00529cf123009ad5" }
  checked := by decide +kernel

theorem w0242_check : PointSegmentLeaf.check w0242.data.points
    (Quadratic3.ofRat w0242.data.radiusSquared) w0242.data.witness = true := w0242.checked

def w0243 : CheckedWitness where
  data := {
    family := .q35
    factId := 17237
    role := 5
    anchorId := 258
    pointIds := [258,170,178,189,198,208,209,210]
    points := [p0208,p0170,p0178,p0189,p0198,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 17238
    identity := "5831162cf7e7a1c0b7153bee24c0b31103c8a5ca4cd35153484a14611c2dbfb6" }
  checked := by decide +kernel

theorem w0243_check : PointSegmentLeaf.check w0243.data.points
    (Quadratic3.ofRat w0243.data.radiusSquared) w0243.data.witness = true := w0243.checked

def w0244 : CheckedWitness where
  data := {
    family := .q35
    factId := 17629
    role := 3
    anchorId := 256
    pointIds := [256,0,1,9,10,11,19,21,50]
    points := [p0000,p0000,p0001,p0009,p0010,p0011,p0019,p0021,p0050]
    radiusSquared := 1/4
    witness := .segment 3 8
    originalFlag := false
    sourceNI := true
    journalLine := 17630
    identity := "52d67e524a9c5f4d58b7bad61520e78af448eab9cc536a0ce6686a3b3171b23d" }
  checked := by decide +kernel

theorem w0244_check : PointSegmentLeaf.check w0244.data.points
    (Quadratic3.ofRat w0244.data.radiusSquared) w0244.data.witness = true := w0244.checked

def w0245 : CheckedWitness where
  data := {
    family := .q35
    factId := 17922
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,10,11,13,14,21,37,45]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0010,p0011,p0013,p0014,p0021,p0037,p0045]
    radiusSquared := 1/4
    witness := .segment 13 14
    originalFlag := false
    sourceNI := true
    journalLine := 17923
    identity := "604793648a170dc42f7c2f983936e7d28bbf37c46686f738070037ee1f7fe741" }
  checked := by decide +kernel

theorem w0245_check : PointSegmentLeaf.check w0245.data.points
    (Quadratic3.ofRat w0245.data.radiusSquared) w0245.data.witness = true := w0245.checked

def w0246 : CheckedWitness where
  data := {
    family := .q35
    factId := 20015
    role := 5
    anchorId := 258
    pointIds := [258,104,198,208,209,210]
    points := [p0208,p0104,p0198,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 20016
    identity := "021aa9f1663b2ab3b85cf2b4101381914abde3038b78b910fc8d533fc4ee7ffa" }
  checked := by decide +kernel

theorem w0246_check : PointSegmentLeaf.check w0246.data.points
    (Quadratic3.ofRat w0246.data.radiusSquared) w0246.data.witness = true := w0246.checked

def w0247 : CheckedWitness where
  data := {
    family := .q35
    factId := 20104
    role := 5
    anchorId := 258
    pointIds := [258,170,177,189,198,201,202,208,209,210,211,212]
    points := [p0208,p0170,p0177,p0189,p0198,p0201,p0202,p0208,p0209,p0210,p0211,p0212]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 20105
    identity := "c44d8c7b99020f0cdeb172c942afc1aed3b3ceab5f794c4d693ded04144276e9" }
  checked := by decide +kernel

theorem w0247_check : PointSegmentLeaf.check w0247.data.points
    (Quadratic3.ofRat w0247.data.radiusSquared) w0247.data.witness = true := w0247.checked

def w0248 : CheckedWitness where
  data := {
    family := .q35
    factId := 20256
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,11,12,21,22,33,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0011,p0012,p0021,p0022,p0033,p0050]
    radiusSquared := 1/4
    witness := .segment 5 11
    originalFlag := false
    sourceNI := true
    journalLine := 20257
    identity := "96d6debac05988707ec5d4860dc4819d5159ce601f90fe0a440bf6449a8785b1" }
  checked := by decide +kernel

theorem w0248_check : PointSegmentLeaf.check w0248.data.points
    (Quadratic3.ofRat w0248.data.radiusSquared) w0248.data.witness = true := w0248.checked

def w0249 : CheckedWitness where
  data := {
    family := .q35
    factId := 20331
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,104]
    points := [p0000,p0000,p0001,p0002,p0009,p0104]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 20332
    identity := "1b601e1c3d845d81ffddbbc2f13767b13adba83696bc86ce5ba02579accc5021" }
  checked := by decide +kernel

theorem w0249_check : PointSegmentLeaf.check w0249.data.points
    (Quadratic3.ofRat w0249.data.radiusSquared) w0249.data.witness = true := w0249.checked

def w0250 : CheckedWitness where
  data := {
    family := .q35
    factId := 20382
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,104]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0104]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 20383
    identity := "037282e09540fb234b6c8ada5dfdf28a16fa0b4c23ec35a1432bdc6b4b1ae48a" }
  checked := by decide +kernel

theorem w0250_check : PointSegmentLeaf.check w0250.data.points
    (Quadratic3.ofRat w0250.data.radiusSquared) w0250.data.witness = true := w0250.checked

def w0251 : CheckedWitness where
  data := {
    family := .q35
    factId := 20387
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,11,12,19,21,22,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0011,p0012,p0019,p0021,p0022,p0050]
    radiusSquared := 1/4
    witness := .segment 4 11
    originalFlag := false
    sourceNI := true
    journalLine := 20388
    identity := "9c5c63806d8a7e8dd2f3ec2bd6208819f2d9965a34facfc0b3fdd603f8e75579" }
  checked := by decide +kernel

theorem w0251_check : PointSegmentLeaf.check w0251.data.points
    (Quadratic3.ofRat w0251.data.radiusSquared) w0251.data.witness = true := w0251.checked

def w0252 : CheckedWitness where
  data := {
    family := .q35
    factId := 20535
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,11,12,19,50]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0011,p0012,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 4 9
    originalFlag := false
    sourceNI := true
    journalLine := 20536
    identity := "5abd2ebc31e07a99fa82696bfae8e45e050095101818ad54a0bf6882cfe42556" }
  checked := by decide +kernel

theorem w0252_check : PointSegmentLeaf.check w0252.data.points
    (Quadratic3.ofRat w0252.data.radiusSquared) w0252.data.witness = true := w0252.checked

def w0253 : CheckedWitness where
  data := {
    family := .q35
    factId := 20680
    role := 5
    anchorId := 258
    pointIds := [258,170,188,198,208,209,210,211]
    points := [p0208,p0170,p0188,p0198,p0208,p0209,p0210,p0211]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 20681
    identity := "c72e2ac6fefbbf94fdece1bea82a99a7562a1b2f1915c08f0aaf97466f054a19" }
  checked := by decide +kernel

theorem w0253_check : PointSegmentLeaf.check w0253.data.points
    (Quadratic3.ofRat w0253.data.radiusSquared) w0253.data.witness = true := w0253.checked

def w0254 : CheckedWitness where
  data := {
    family := .q35
    factId := 21431
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198,199,200,208,209,210,211]
    points := [p0208,p0170,p0187,p0198,p0199,p0200,p0208,p0209,p0210,p0211]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 21432
    identity := "196fe1eab50e40475386a5eed4fd56cf41d2674bd8b5745ffee9908f4e0ea164" }
  checked := by decide +kernel

theorem w0254_check : PointSegmentLeaf.check w0254.data.points
    (Quadratic3.ofRat w0254.data.radiusSquared) w0254.data.witness = true := w0254.checked

def w0255 : CheckedWitness where
  data := {
    family := .q35
    factId := 24536
    role := 5
    anchorId := 258
    pointIds := [258,162,170,198,208,209,210]
    points := [p0208,p0162,p0170,p0198,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 24537
    identity := "e41cb7aec887868e9b7c57c3fea554cfdf4a198f14eca9de14c1977fb15bd97b" }
  checked := by decide +kernel

theorem w0255_check : PointSegmentLeaf.check w0255.data.points
    (Quadratic3.ofRat w0255.data.radiusSquared) w0255.data.witness = true := w0255.checked

def w0256 : CheckedWitness where
  data := {
    family := .q35
    factId := 25821
    role := 3
    anchorId := 256
    pointIds := [256,0,1,3,9,10,20,50]
    points := [p0000,p0000,p0001,p0003,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 4 7
    originalFlag := false
    sourceNI := true
    journalLine := 25822
    identity := "1e340766ab126068d249b2b6fc99c608c16640376a4fe0e74284a2d2bb679e63" }
  checked := by decide +kernel

theorem w0256_check : PointSegmentLeaf.check w0256.data.points
    (Quadratic3.ofRat w0256.data.radiusSquared) w0256.data.witness = true := w0256.checked

def w0257 : CheckedWitness where
  data := {
    family := .q35
    factId := 25949
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,9,10,11,12,13,19,21,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0009,p0010,p0011,p0012,p0013,p0019,p0021,p0050]
    radiusSquared := 1/4
    witness := .segment 6 13
    originalFlag := false
    sourceNI := true
    journalLine := 25950
    identity := "59e53da3c55de6981cee06068b98a850d2d91c04975a961d935b6435ce851de7" }
  checked := by decide +kernel

theorem w0257_check : PointSegmentLeaf.check w0257.data.points
    (Quadratic3.ofRat w0257.data.radiusSquared) w0257.data.witness = true := w0257.checked

def w0258 : CheckedWitness where
  data := {
    family := .q35
    factId := 26232
    role := 5
    anchorId := 258
    pointIds := [258,170,175,198,199,200,208,209,210]
    points := [p0208,p0170,p0175,p0198,p0199,p0200,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 26233
    identity := "7b03e4a8524e4fee3e655ad0fa6f2a0d54bc44159773dc02627846ee10f7de41" }
  checked := by decide +kernel

theorem w0258_check : PointSegmentLeaf.check w0258.data.points
    (Quadratic3.ofRat w0258.data.radiusSquared) w0258.data.witness = true := w0258.checked

def w0259 : CheckedWitness where
  data := {
    family := .q35
    factId := 26461
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198,208,209,210]
    points := [p0208,p0170,p0187,p0198,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 26462
    identity := "ae141b4801702adabe9f296fdd489438022371f6c918fcd45e89775d796728ec" }
  checked := by decide +kernel

theorem w0259_check : PointSegmentLeaf.check w0259.data.points
    (Quadratic3.ofRat w0259.data.radiusSquared) w0259.data.witness = true := w0259.checked

def w0260 : CheckedWitness where
  data := {
    family := .q35
    factId := 29862
    role := 3
    anchorId := 256
    pointIds := [256,0,1,4,9,20,50]
    points := [p0000,p0000,p0001,p0004,p0009,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 4 6
    originalFlag := false
    sourceNI := true
    journalLine := 29863
    identity := "3bbe487acf2eb0538c4eb777f658207fddcf78f6103dd77d60db58f9662e655c" }
  checked := by decide +kernel

theorem w0260_check : PointSegmentLeaf.check w0260.data.points
    (Quadratic3.ofRat w0260.data.radiusSquared) w0260.data.witness = true := w0260.checked

def w0261 : CheckedWitness where
  data := {
    family := .q35
    factId := 30679
    role := 5
    anchorId := 258
    pointIds := [258,104,208,209,210]
    points := [p0208,p0104,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 30680
    identity := "9c6f515d14a4b28f551ecc35d4af288be3ee160e0e426ee3dd4c7d97c5cf76c2" }
  checked := by decide +kernel

theorem w0261_check : PointSegmentLeaf.check w0261.data.points
    (Quadratic3.ofRat w0261.data.radiusSquared) w0261.data.witness = true := w0261.checked

def w0262 : CheckedWitness where
  data := {
    family := .q35
    factId := 31935
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,42,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0042,p0050]
    radiusSquared := 1/4
    witness := .segment 5 8
    originalFlag := false
    sourceNI := true
    journalLine := 31936
    identity := "162e0205a6f3802d5fa5bacb3dfa20bc0998b9dd126d71db686ba177355ef400" }
  checked := by decide +kernel

theorem w0262_check : PointSegmentLeaf.check w0262.data.points
    (Quadratic3.ofRat w0262.data.radiusSquared) w0262.data.witness = true := w0262.checked

def w0263 : CheckedWitness where
  data := {
    family := .q35
    factId := 31974
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,42,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0042,p0050]
    radiusSquared := 1/4
    witness := .segment 5 9
    originalFlag := false
    sourceNI := true
    journalLine := 31975
    identity := "fedf305e288e01574297415f039c48837ff174c93858cd845d83477725f2c8cf" }
  checked := by decide +kernel

theorem w0263_check : PointSegmentLeaf.check w0263.data.points
    (Quadratic3.ofRat w0263.data.radiusSquared) w0263.data.witness = true := w0263.checked

def w0264 : CheckedWitness where
  data := {
    family := .q35
    factId := 32031
    role := 5
    anchorId := 258
    pointIds := [258,170,199,200,205,208,209,210,211]
    points := [p0208,p0170,p0199,p0200,p0205,p0208,p0209,p0210,p0211]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 32032
    identity := "260a50f6f6d3d629d1b4db7c75034a7323d94c460eb282f43245b7f7d616a9cd" }
  checked := by decide +kernel

theorem w0264_check : PointSegmentLeaf.check w0264.data.points
    (Quadratic3.ofRat w0264.data.radiusSquared) w0264.data.witness = true := w0264.checked

def w0265 : CheckedWitness where
  data := {
    family := .q35
    factId := 32238
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 5 9
    originalFlag := false
    sourceNI := true
    journalLine := 32239
    identity := "6c7839ac2a4d352a13aaddc8247e00228ab16214c65f2b8c12b643bcbdf04c6f" }
  checked := by decide +kernel

theorem w0265_check : PointSegmentLeaf.check w0265.data.points
    (Quadratic3.ofRat w0265.data.radiusSquared) w0265.data.witness = true := w0265.checked

def w0266 : CheckedWitness where
  data := {
    family := .q35
    factId := 32875
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,42,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0042,p0050]
    radiusSquared := 1/4
    witness := .segment 5 7
    originalFlag := false
    sourceNI := true
    journalLine := 32876
    identity := "a879fb78b1c7eaf2e352206a52d6211401e29e52e8462756d5aa52561a889c4a" }
  checked := by decide +kernel

theorem w0266_check : PointSegmentLeaf.check w0266.data.points
    (Quadratic3.ofRat w0266.data.radiusSquared) w0266.data.witness = true := w0266.checked

def w0267 : CheckedWitness where
  data := {
    family := .q35
    factId := 32891
    role := 5
    anchorId := 258
    pointIds := [258,104,198,199,208,209,210]
    points := [p0208,p0104,p0198,p0199,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 32892
    identity := "b7971ccfaeeeff6652501ba1c5f634cd7b9dc6cb5dcfe7284665e048fda16ace" }
  checked := by decide +kernel

theorem w0267_check : PointSegmentLeaf.check w0267.data.points
    (Quadratic3.ofRat w0267.data.radiusSquared) w0267.data.witness = true := w0267.checked

def w0268 : CheckedWitness where
  data := {
    family := .q35
    factId := 33004
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,11,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0011,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 5 8
    originalFlag := false
    sourceNI := true
    journalLine := 33005
    identity := "c5b8ab4962db8cba0eb437d8346608dcba136746dedc546b23cd6892e7d789f4" }
  checked := by decide +kernel

theorem w0268_check : PointSegmentLeaf.check w0268.data.points
    (Quadratic3.ofRat w0268.data.radiusSquared) w0268.data.witness = true := w0268.checked

def w0269 : CheckedWitness where
  data := {
    family := .q35
    factId := 34493
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,11,12,19,20,21,22,30,31,32,33,36,44,45,58]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0011,p0012,p0019,p0020,p0021,p0022,p0030,p0031,p0032,p0033,p0036,p0044,p0045,p0058]
    radiusSquared := 1/4
    witness := .segment 16 19
    originalFlag := false
    sourceNI := true
    journalLine := 34494
    identity := "ab9b2bd2fa788b0778e7dfb1c19404d0d10dcf3dd4b447d4ade38774e1834ae4" }
  checked := by decide +kernel

theorem w0269_check : PointSegmentLeaf.check w0269.data.points
    (Quadratic3.ofRat w0269.data.radiusSquared) w0269.data.witness = true := w0269.checked

def w0270 : CheckedWitness where
  data := {
    family := .q35
    factId := 37602
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,9,11,12,13,14,19,20,21,22,24,30,31,32,72]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0009,p0011,p0012,p0013,p0014,p0019,p0020,p0021,p0022,p0024,p0030,p0031,p0032,p0072]
    radiusSquared := 1/4
    witness := .segment 15 19
    originalFlag := false
    sourceNI := true
    journalLine := 37603
    identity := "a1619b1f5c122a669069f0d3f6264758958c331ab0b430cdbf5f7045e429e28d" }
  checked := by decide +kernel

theorem w0270_check : PointSegmentLeaf.check w0270.data.points
    (Quadratic3.ofRat w0270.data.radiusSquared) w0270.data.witness = true := w0270.checked

def w0271 : CheckedWitness where
  data := {
    family := .q35
    factId := 37887
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,9,11,12,13,19,20,21,22,24,30,31,72]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0009,p0011,p0012,p0013,p0019,p0020,p0021,p0022,p0024,p0030,p0031,p0072]
    radiusSquared := 1/4
    witness := .segment 14 17
    originalFlag := false
    sourceNI := true
    journalLine := 37888
    identity := "9caa259d4e63bd52a66b46e4b8b5c5523e6e42f936efd5937b8898a45460bb3e" }
  checked := by decide +kernel

theorem w0271_check : PointSegmentLeaf.check w0271.data.points
    (Quadratic3.ofRat w0271.data.radiusSquared) w0271.data.witness = true := w0271.checked

def w0272 : CheckedWitness where
  data := {
    family := .q35
    factId := 38861
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,11,19,21,30,31,32,36,42,44,58]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0011,p0019,p0021,p0030,p0031,p0032,p0036,p0042,p0044,p0058]
    radiusSquared := 1/4
    witness := .segment 12 15
    originalFlag := false
    sourceNI := true
    journalLine := 38862
    identity := "2486905dd10e2621c9e5178cb0c9f689911a27529333f5ebb26e5f387f6f32a6" }
  checked := by decide +kernel

theorem w0272_check : PointSegmentLeaf.check w0272.data.points
    (Quadratic3.ofRat w0272.data.radiusSquared) w0272.data.witness = true := w0272.checked

def w0273 : CheckedWitness where
  data := {
    family := .q35
    factId := 38927
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,11,19,20,21,30,31,32,36,43,44,57,58]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0011,p0019,p0020,p0021,p0030,p0031,p0032,p0036,p0043,p0044,p0057,p0058]
    radiusSquared := 1/4
    witness := .segment 13 16
    originalFlag := false
    sourceNI := true
    journalLine := 38928
    identity := "f483695e0d43809123e117c70b445547c32d8708940adfa12373829761a16b7a" }
  checked := by decide +kernel

theorem w0273_check : PointSegmentLeaf.check w0273.data.points
    (Quadratic3.ofRat w0273.data.radiusSquared) w0273.data.witness = true := w0273.checked

def w0274 : CheckedWitness where
  data := {
    family := .q35
    factId := 40645
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,19,21,30,32,36,42,43,44,57]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0019,p0021,p0030,p0032,p0036,p0042,p0043,p0044,p0057]
    radiusSquared := 1/4
    witness := .segment 12 16
    originalFlag := false
    sourceNI := true
    journalLine := 40646
    identity := "0f2dadd155e414442f260771dabbf80785095d76e8231d5d6815062a7b782014" }
  checked := by decide +kernel

theorem w0274_check : PointSegmentLeaf.check w0274.data.points
    (Quadratic3.ofRat w0274.data.radiusSquared) w0274.data.witness = true := w0274.checked

def w0275 : CheckedWitness where
  data := {
    family := .q35
    factId := 40677
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,19,30,31,36,42,57]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0019,p0030,p0031,p0036,p0042,p0057]
    radiusSquared := 1/4
    witness := .segment 11 13
    originalFlag := false
    sourceNI := true
    journalLine := 40678
    identity := "db8f55a0ff829b17401893e1160c6f0d40fcea9bf8005a9b8296832f5dc33798" }
  checked := by decide +kernel

theorem w0275_check : PointSegmentLeaf.check w0275.data.points
    (Quadratic3.ofRat w0275.data.radiusSquared) w0275.data.witness = true := w0275.checked

def w0276 : CheckedWitness where
  data := {
    family := .q35
    factId := 42856
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 5 7
    originalFlag := false
    sourceNI := true
    journalLine := 42857
    identity := "f0666666b1e4e01f6bafb81df1db186214913a27feefde23c9b8d19023fc39ee" }
  checked := by decide +kernel

theorem w0276_check : PointSegmentLeaf.check w0276.data.points
    (Quadratic3.ofRat w0276.data.radiusSquared) w0276.data.witness = true := w0276.checked

def w0277 : CheckedWitness where
  data := {
    family := .q35
    factId := 43644
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,9,10,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0009,p0010,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 6 9
    originalFlag := false
    sourceNI := true
    journalLine := 43645
    identity := "c0199ce220082c18dd48113ff2ec33b1c7089e2109fb2a3603ef617725e29c02" }
  checked := by decide +kernel

theorem w0277_check : PointSegmentLeaf.check w0277.data.points
    (Quadratic3.ofRat w0277.data.radiusSquared) w0277.data.witness = true := w0277.checked

def w0278 : CheckedWitness where
  data := {
    family := .q35
    factId := 43824
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,11,12,19,22,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0011,p0012,p0019,p0022,p0050]
    radiusSquared := 1/4
    witness := .segment 5 11
    originalFlag := false
    sourceNI := true
    journalLine := 43825
    identity := "c18894ff5b792ee55ef36b21fcc51bafcb2e6059a91199b95e0f161b522f5b0e" }
  checked := by decide +kernel

theorem w0278_check : PointSegmentLeaf.check w0278.data.points
    (Quadratic3.ofRat w0278.data.radiusSquared) w0278.data.witness = true := w0278.checked

def w0279 : CheckedWitness where
  data := {
    family := .q35
    factId := 43874
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,5,9,11,12,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0005,p0009,p0011,p0012,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 6 10
    originalFlag := false
    sourceNI := true
    journalLine := 43875
    identity := "3f6ebc1fd53795b7dc2c540c550c841c29a9dd81eb134297fc446c2598ca5eba" }
  checked := by decide +kernel

theorem w0279_check : PointSegmentLeaf.check w0279.data.points
    (Quadratic3.ofRat w0279.data.radiusSquared) w0279.data.witness = true := w0279.checked

def w0280 : CheckedWitness where
  data := {
    family := .q35
    factId := 44053
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,5,9,10,11,19,21,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0005,p0009,p0010,p0011,p0019,p0021,p0050]
    radiusSquared := 1/4
    witness := .segment 6 11
    originalFlag := false
    sourceNI := true
    journalLine := 44054
    identity := "49f062353d49f35fb71492757f0ff4e9d832c79b70da5ed49c71f0a71a7942d4" }
  checked := by decide +kernel

theorem w0280_check : PointSegmentLeaf.check w0280.data.points
    (Quadratic3.ofRat w0280.data.radiusSquared) w0280.data.witness = true := w0280.checked

def w0281 : CheckedWitness where
  data := {
    family := .q35
    factId := 44067
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,5,9,10,11,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0005,p0009,p0010,p0011,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 6 10
    originalFlag := false
    sourceNI := true
    journalLine := 44068
    identity := "73b603697ea793520bf9efbdf6d39311deb2688754ce56c3293a544f8329eabf" }
  checked := by decide +kernel

theorem w0281_check : PointSegmentLeaf.check w0281.data.points
    (Quadratic3.ofRat w0281.data.radiusSquared) w0281.data.witness = true := w0281.checked

def w0282 : CheckedWitness where
  data := {
    family := .q35
    factId := 50825
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,11,12,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0011,p0012,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 7 11
    originalFlag := false
    sourceNI := true
    journalLine := 50826
    identity := "16eba2b4f8bd03859322779c79d4af2b4ec2a0b79ea1657d91ce0791d7830be2" }
  checked := by decide +kernel

theorem w0282_check : PointSegmentLeaf.check w0282.data.points
    (Quadratic3.ofRat w0282.data.radiusSquared) w0282.data.witness = true := w0282.checked

def w0283 : CheckedWitness where
  data := {
    family := .q35
    factId := 51170
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,10,11,12,20,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0010,p0011,p0012,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 7 12
    originalFlag := false
    sourceNI := true
    journalLine := 51171
    identity := "6cfbcd283dc6c7960bf7cf093ca5405411159b46d6e5fff334f2d6fc475ebd23" }
  checked := by decide +kernel

theorem w0283_check : PointSegmentLeaf.check w0283.data.points
    (Quadratic3.ofRat w0283.data.radiusSquared) w0283.data.witness = true := w0283.checked

def w0284 : CheckedWitness where
  data := {
    family := .q35
    factId := 51250
    role := 5
    anchorId := 258
    pointIds := [258,104,188,198,199,200,208,209]
    points := [p0208,p0104,p0188,p0198,p0199,p0200,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 51251
    identity := "b783bd4306dd3e26d23bb969fd541d25331eeea13abdeb1f31af5d5c293c3551" }
  checked := by decide +kernel

theorem w0284_check : PointSegmentLeaf.check w0284.data.points
    (Quadratic3.ofRat w0284.data.radiusSquared) w0284.data.witness = true := w0284.checked

def w0285 : CheckedWitness where
  data := {
    family := .q35
    factId := 51718
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,5,9,10,11,12,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0005,p0009,p0010,p0011,p0012,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 6 11
    originalFlag := false
    sourceNI := true
    journalLine := 51719
    identity := "0ffa0b7972b9415cae7dffb85d91d087d31f3a4364cf1c5662b5d957f50eb5db" }
  checked := by decide +kernel

theorem w0285_check : PointSegmentLeaf.check w0285.data.points
    (Quadratic3.ofRat w0285.data.radiusSquared) w0285.data.witness = true := w0285.checked

def w0286 : CheckedWitness where
  data := {
    family := .q35
    factId := 53028
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,5,9,10,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0005,p0009,p0010,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 6 9
    originalFlag := false
    sourceNI := true
    journalLine := 53029
    identity := "f5f57b7b654cae274ff23e5708d4e7c0df0390d828b9d71336e633c29e044f70" }
  checked := by decide +kernel

theorem w0286_check : PointSegmentLeaf.check w0286.data.points
    (Quadratic3.ofRat w0286.data.radiusSquared) w0286.data.witness = true := w0286.checked

def w0287 : CheckedWitness where
  data := {
    family := .q35
    factId := 53104
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,11,12,15,72]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0011,p0012,p0015,p0072]
    radiusSquared := 1/4
    witness := .segment 10 11
    originalFlag := false
    sourceNI := true
    journalLine := 53105
    identity := "a371b38f8032289be8064a3473776cf0ab4299a6679688e86194b6541cb38c77" }
  checked := by decide +kernel

theorem w0287_check : PointSegmentLeaf.check w0287.data.points
    (Quadratic3.ofRat w0287.data.radiusSquared) w0287.data.witness = true := w0287.checked

def w0288 : CheckedWitness where
  data := {
    family := .q35
    factId := 53173
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,10,11,12,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0010,p0011,p0012,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 7 12
    originalFlag := false
    sourceNI := true
    journalLine := 53174
    identity := "444915e8f480ec8f640f5aefa10723306d3e84d43019b63c53e3f9a0b720cb74" }
  checked := by decide +kernel

theorem w0288_check : PointSegmentLeaf.check w0288.data.points
    (Quadratic3.ofRat w0288.data.radiusSquared) w0288.data.witness = true := w0288.checked

def w0289 : CheckedWitness where
  data := {
    family := .q35
    factId := 53963
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,11,12,13,15,22,23,34,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0011,p0012,p0013,p0015,p0022,p0023,p0034,p0050]
    radiusSquared := 1/4
    witness := .segment 7 15
    originalFlag := false
    sourceNI := true
    journalLine := 53964
    identity := "9b50400de476cf8e6d7557de01f54c3156f1e240331b40395cba4086cefe6a7d" }
  checked := by decide +kernel

theorem w0289_check : PointSegmentLeaf.check w0289.data.points
    (Quadratic3.ofRat w0289.data.radiusSquared) w0289.data.witness = true := w0289.checked

def w0290 : CheckedWitness where
  data := {
    family := .q35
    factId := 54428
    role := 5
    anchorId := 258
    pointIds := [258,170,199,200,205,208,209,210,211,212,214]
    points := [p0208,p0170,p0199,p0200,p0205,p0208,p0209,p0210,p0211,p0212,p0214]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 54429
    identity := "953f422916f19d2b8e5bd3e5b62dd711d093b579985ebd2056fdff7570eb11a8" }
  checked := by decide +kernel

theorem w0290_check : PointSegmentLeaf.check w0290.data.points
    (Quadratic3.ofRat w0290.data.radiusSquared) w0290.data.witness = true := w0290.checked

def w0291 : CheckedWitness where
  data := {
    family := .q35
    factId := 54495
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,9,10,20,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 6 9
    originalFlag := false
    sourceNI := true
    journalLine := 54496
    identity := "15085fa552a6d1e51256fade60e92ab1f7df4cfc8069cb32115f106df8c5549e" }
  checked := by decide +kernel

theorem w0291_check : PointSegmentLeaf.check w0291.data.points
    (Quadratic3.ofRat w0291.data.radiusSquared) w0291.data.witness = true := w0291.checked

def w0292 : CheckedWitness where
  data := {
    family := .q35
    factId := 54825
    role := 5
    anchorId := 258
    pointIds := [258,170,179,200,205,208,209,210,211,212,214]
    points := [p0208,p0170,p0179,p0200,p0205,p0208,p0209,p0210,p0211,p0212,p0214]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 54826
    identity := "3fcb14bb7683f3ca55fa4b6f89831520cb5eb566e1b7af475e0a54bc772ff45d" }
  checked := by decide +kernel

theorem w0292_check : PointSegmentLeaf.check w0292.data.points
    (Quadratic3.ofRat w0292.data.radiusSquared) w0292.data.witness = true := w0292.checked

def w0293 : CheckedWitness where
  data := {
    family := .q35
    factId := 55325
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,19,20,30,31,32,37,43,44,57]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0019,p0020,p0030,p0031,p0032,p0037,p0043,p0044,p0057]
    radiusSquared := 1/4
    witness := .segment 11 14
    originalFlag := false
    sourceNI := true
    journalLine := 55326
    identity := "60701c8255689cb0910608141a41258afb39528dd9126bfddc85dc65fe3ae4df" }
  checked := by decide +kernel

theorem w0293_check : PointSegmentLeaf.check w0293.data.points
    (Quadratic3.ofRat w0293.data.radiusSquared) w0293.data.witness = true := w0293.checked

def w0294 : CheckedWitness where
  data := {
    family := .q35
    factId := 55330
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,9,10,19,20,30,31,32,35,43,44,57,72]
    points := [p0000,p0000,p0001,p0002,p0009,p0010,p0019,p0020,p0030,p0031,p0032,p0035,p0043,p0044,p0057,p0072]
    radiusSquared := 1/4
    witness := .segment 11 15
    originalFlag := false
    sourceNI := true
    journalLine := 55331
    identity := "0bbf444ac71ef924ffc053723b0b36202c2a7291fc821572faede92742825fd3" }
  checked := by decide +kernel

theorem w0294_check : PointSegmentLeaf.check w0294.data.points
    (Quadratic3.ofRat w0294.data.radiusSquared) w0294.data.witness = true := w0294.checked

def w0295 : CheckedWitness where
  data := {
    family := .q35
    factId := 55576
    role := 5
    anchorId := 258
    pointIds := [258,170,199,200,205,208,209,210,211,214]
    points := [p0208,p0170,p0199,p0200,p0205,p0208,p0209,p0210,p0211,p0214]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 55577
    identity := "b36970212146fa519f04fd9b160ea7a479f084b111e918c031ee800b5ef9d4b9" }
  checked := by decide +kernel

theorem w0295_check : PointSegmentLeaf.check w0295.data.points
    (Quadratic3.ofRat w0295.data.radiusSquared) w0295.data.witness = true := w0295.checked

def w0296 : CheckedWitness where
  data := {
    family := .q35
    factId := 56223
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,9,10,12,19,30,31,36,42,43,57]
    points := [p0000,p0000,p0001,p0002,p0003,p0009,p0010,p0012,p0019,p0030,p0031,p0036,p0042,p0043,p0057]
    radiusSquared := 1/4
    witness := .segment 11 14
    originalFlag := false
    sourceNI := true
    journalLine := 56224
    identity := "b1628b3f0c1b636c188b497ac468158ec32369a470ebb0b06b8da42bb93852c0" }
  checked := by decide +kernel

theorem w0296_check : PointSegmentLeaf.check w0296.data.points
    (Quadratic3.ofRat w0296.data.radiusSquared) w0296.data.witness = true := w0296.checked

def w0297 : CheckedWitness where
  data := {
    family := .q35
    factId := 56384
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,5,9,10,11,20,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0005,p0009,p0010,p0011,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 6 10
    originalFlag := false
    sourceNI := true
    journalLine := 56385
    identity := "10d6c45281f5a43ca8d510bc90285236a7d3a958f551b2baa6e54adaf5cc3210" }
  checked := by decide +kernel

theorem w0297_check : PointSegmentLeaf.check w0297.data.points
    (Quadratic3.ofRat w0297.data.radiusSquared) w0297.data.witness = true := w0297.checked

def w0298 : CheckedWitness where
  data := {
    family := .q35
    factId := 56568
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,5,9,10,20,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0005,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 6 9
    originalFlag := false
    sourceNI := true
    journalLine := 56569
    identity := "a1e0300fc01c525696c01cdac010dc5f32ed24fc122ba87ccdb7ef575f99e559" }
  checked := by decide +kernel

theorem w0298_check : PointSegmentLeaf.check w0298.data.points
    (Quadratic3.ofRat w0298.data.radiusSquared) w0298.data.witness = true := w0298.checked

def w0299 : CheckedWitness where
  data := {
    family := .q35
    factId := 56636
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,10,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0010,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 7 10
    originalFlag := false
    sourceNI := true
    journalLine := 56637
    identity := "98dafae95efcd86d18e8816f14205f1f5ef00e99d231c7ea412a1903406ef655" }
  checked := by decide +kernel

theorem w0299_check : PointSegmentLeaf.check w0299.data.points
    (Quadratic3.ofRat w0299.data.radiusSquared) w0299.data.witness = true := w0299.checked

def w0300 : CheckedWitness where
  data := {
    family := .q35
    factId := 57421
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,10,20,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0010,p0020,p0050]
    radiusSquared := 1/4
    witness := .segment 7 10
    originalFlag := false
    sourceNI := true
    journalLine := 57422
    identity := "e2770d4635c2000c42621f7baf1103e644e8677df7ad0e7a9fa230f04a54b6a4" }
  checked := by decide +kernel

theorem w0300_check : PointSegmentLeaf.check w0300.data.points
    (Quadratic3.ofRat w0300.data.radiusSquared) w0300.data.witness = true := w0300.checked

def w0301 : CheckedWitness where
  data := {
    family := .q35
    factId := 57692
    role := 5
    anchorId := 258
    pointIds := [258,170,175,198,199,208,209]
    points := [p0208,p0170,p0175,p0198,p0199,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 57693
    identity := "fe9d24fe48443ca6789e9a6051158d5498d6dd245c0c95a322a2da4ed9313a64" }
  checked := by decide +kernel

theorem w0301_check : PointSegmentLeaf.check w0301.data.points
    (Quadratic3.ofRat w0301.data.radiusSquared) w0301.data.witness = true := w0301.checked

def w0302 : CheckedWitness where
  data := {
    family := .q35
    factId := 57781
    role := 5
    anchorId := 258
    pointIds := [258,170,175,198,199,208,209,210]
    points := [p0208,p0170,p0175,p0198,p0199,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 57782
    identity := "155d4e2e48f9bd5e1efe84a9b5ad9bfbafd20958e829a9126f4f8fd8907ad167" }
  checked := by decide +kernel

theorem w0302_check : PointSegmentLeaf.check w0302.data.points
    (Quadratic3.ofRat w0302.data.radiusSquared) w0302.data.witness = true := w0302.checked

def w0303 : CheckedWitness where
  data := {
    family := .q35
    factId := 57791
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,10,11,12,13,14,22,23,24,34,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0010,p0011,p0012,p0013,p0014,p0022,p0023,p0024,p0034,p0050]
    radiusSquared := 1/4
    witness := .segment 7 17
    originalFlag := false
    sourceNI := true
    journalLine := 57792
    identity := "d97faec83e03ee39042e0a082fb85559176e9e7526b2ac419496257907cc76b2" }
  checked := by decide +kernel

theorem w0303_check : PointSegmentLeaf.check w0303.data.points
    (Quadratic3.ofRat w0303.data.radiusSquared) w0303.data.witness = true := w0303.checked

def w0304 : CheckedWitness where
  data := {
    family := .q35
    factId := 57798
    role := 5
    anchorId := 258
    pointIds := [258,170,188,198,208]
    points := [p0208,p0170,p0188,p0198,p0208]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 57799
    identity := "98f7d7fa7b7bd42990c9778b0b771435bd9722f029a955b26c38a9a61c5e3ae8" }
  checked := by decide +kernel

theorem w0304_check : PointSegmentLeaf.check w0304.data.points
    (Quadratic3.ofRat w0304.data.radiusSquared) w0304.data.witness = true := w0304.checked

def w0305 : CheckedWitness where
  data := {
    family := .q35
    factId := 57946
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,5,9,11,12,13,14,15,22,26,46]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0005,p0009,p0011,p0012,p0013,p0014,p0015,p0022,p0026,p0046]
    radiusSquared := 1/4
    witness := .segment 14 15
    originalFlag := false
    sourceNI := true
    journalLine := 57947
    identity := "8aae778ee34b7e64a2cdb5c2e21249c3d1c869638e2bd778b78806c12052cb54" }
  checked := by decide +kernel

theorem w0305_check : PointSegmentLeaf.check w0305.data.points
    (Quadratic3.ofRat w0305.data.radiusSquared) w0305.data.witness = true := w0305.checked

def w0306 : CheckedWitness where
  data := {
    family := .q35
    factId := 58135
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,3,4,9,19,50]
    points := [p0000,p0000,p0001,p0002,p0003,p0004,p0009,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 6 8
    originalFlag := false
    sourceNI := true
    journalLine := 58136
    identity := "d799fff970425ac1e06e50cab50be88f3fdcf85f2a484c797f792d61cb8b300e" }
  checked := by decide +kernel

theorem w0306_check : PointSegmentLeaf.check w0306.data.points
    (Quadratic3.ofRat w0306.data.radiusSquared) w0306.data.witness = true := w0306.checked

def w0307 : CheckedWitness where
  data := {
    family := .q35
    factId := 59325
    role := 5
    anchorId := 258
    pointIds := [258,104,187,198,199,208,209,210]
    points := [p0208,p0104,p0187,p0198,p0199,p0208,p0209,p0210]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 59326
    identity := "212affa8d228bbbda241bc78beaa7f07826d53f6138ea120424ead0c3122a043" }
  checked := by decide +kernel

theorem w0307_check : PointSegmentLeaf.check w0307.data.points
    (Quadratic3.ofRat w0307.data.radiusSquared) w0307.data.witness = true := w0307.checked

def w0308 : CheckedWitness where
  data := {
    family := .q35
    factId := 61720
    role := 5
    anchorId := 258
    pointIds := [258,170,175,198,208,209]
    points := [p0208,p0170,p0175,p0198,p0208,p0209]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 61721
    identity := "0e1cf765cf7dffa69f13bfaa252e2514299e9588ef4adc0fc7209bdb79278b21" }
  checked := by decide +kernel

theorem w0308_check : PointSegmentLeaf.check w0308.data.points
    (Quadratic3.ofRat w0308.data.radiusSquared) w0308.data.witness = true := w0308.checked

def w0309 : CheckedWitness where
  data := {
    family := .q35
    factId := 61766
    role := 5
    anchorId := 258
    pointIds := [258,170,187,198,208]
    points := [p0208,p0170,p0187,p0198,p0208]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 61767
    identity := "689aa06bddf63609cf3d0c6a4bde3678f40c061fa40f6959b08721e2edf68a4d" }
  checked := by decide +kernel

theorem w0309_check : PointSegmentLeaf.check w0309.data.points
    (Quadratic3.ofRat w0309.data.radiusSquared) w0309.data.witness = true := w0309.checked

def w0310 : CheckedWitness where
  data := {
    family := .q35
    factId := 63332
    role := 3
    anchorId := 256
    pointIds := [256,0,1,2,19,50]
    points := [p0000,p0000,p0001,p0002,p0019,p0050]
    radiusSquared := 1/4
    witness := .segment 4 5
    originalFlag := false
    sourceNI := true
    journalLine := 63333
    identity := "e4450ff3aab3ea805b4bcf8d9e1ffb287d8bd6f6ff0465ec3b80a35f963e05f8" }
  checked := by decide +kernel

theorem w0310_check : PointSegmentLeaf.check w0310.data.points
    (Quadratic3.ofRat w0310.data.radiusSquared) w0310.data.witness = true := w0310.checked

def w0311 : CheckedWitness where
  data := {
    family := .q45
    factId := 174
    role := 4
    anchorId := 370
    pointIds := [370,47]
    points := [p0100,p0047]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 175
    identity := "4af8e7a1b50c677b6f76eb8f56b152181f9957e9e523cbeb29c1664ac37df529" }
  checked := by decide +kernel

theorem w0311_check : PointSegmentLeaf.check w0311.data.points
    (Quadratic3.ofRat w0311.data.radiusSquared) w0311.data.witness = true := w0311.checked

def w0312 : CheckedWitness where
  data := {
    family := .q45
    factId := 219
    role := 4
    anchorId := 370
    pointIds := [370,59]
    points := [p0100,p0059]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 220
    identity := "8a00495b71444bb0edc8c8d11b2510c1bacae1eb028a09286d5e8817616ce8f8" }
  checked := by decide +kernel

theorem w0312_check : PointSegmentLeaf.check w0312.data.points
    (Quadratic3.ofRat w0312.data.radiusSquared) w0312.data.witness = true := w0312.checked

def w0313 : CheckedWitness where
  data := {
    family := .q45
    factId := 223
    role := 4
    anchorId := 370
    pointIds := [370,60]
    points := [p0100,p0060]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 224
    identity := "82018b37b51155dc0d7a4359eaae0f04e6a5af6f009c25ea73f67642b1885430" }
  checked := by decide +kernel

theorem w0313_check : PointSegmentLeaf.check w0313.data.points
    (Quadratic3.ofRat w0313.data.radiusSquared) w0313.data.witness = true := w0313.checked

def w0314 : CheckedWitness where
  data := {
    family := .q45
    factId := 227
    role := 4
    anchorId := 370
    pointIds := [370,61]
    points := [p0100,p0061]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 228
    identity := "ee29d3de26862c94ef1b76dac695261537bf4ec4e06498b680582dcb2900e756" }
  checked := by decide +kernel

theorem w0314_check : PointSegmentLeaf.check w0314.data.points
    (Quadratic3.ofRat w0314.data.radiusSquared) w0314.data.witness = true := w0314.checked

def w0315 : CheckedWitness where
  data := {
    family := .q45
    factId := 273
    role := 4
    anchorId := 370
    pointIds := [370,73]
    points := [p0100,p0073]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 274
    identity := "f9b8f3ee939a76c11156912ebb7539347d48c43b8cc23657d7a00f799663b7ae" }
  checked := by decide +kernel

theorem w0315_check : PointSegmentLeaf.check w0315.data.points
    (Quadratic3.ofRat w0315.data.radiusSquared) w0315.data.witness = true := w0315.checked

def w0316 : CheckedWitness where
  data := {
    family := .q45
    factId := 277
    role := 4
    anchorId := 370
    pointIds := [370,74]
    points := [p0100,p0074]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 278
    identity := "db7694aea3a572eb1b29a8f0a8144555b59301a6e6b22340825c0d5119731c57" }
  checked := by decide +kernel

theorem w0316_check : PointSegmentLeaf.check w0316.data.points
    (Quadratic3.ofRat w0316.data.radiusSquared) w0316.data.witness = true := w0316.checked

def w0317 : CheckedWitness where
  data := {
    family := .q45
    factId := 281
    role := 4
    anchorId := 370
    pointIds := [370,75]
    points := [p0100,p0075]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 282
    identity := "3b2af5b7e2f9ab1ef4b82bfdf191e421336c84245b54c6ce11e321395503e660" }
  checked := by decide +kernel

theorem w0317_check : PointSegmentLeaf.check w0317.data.points
    (Quadratic3.ofRat w0317.data.radiusSquared) w0317.data.witness = true := w0317.checked

def w0318 : CheckedWitness where
  data := {
    family := .q45
    factId := 330
    role := 4
    anchorId := 370
    pointIds := [370,88]
    points := [p0100,p0088]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 331
    identity := "75fb99594781ba1b1facbd760b120dd1ad06abbf67d653e059584e14efc64b4b" }
  checked := by decide +kernel

theorem w0318_check : PointSegmentLeaf.check w0318.data.points
    (Quadratic3.ofRat w0318.data.radiusSquared) w0318.data.witness = true := w0318.checked

def w0319 : CheckedWitness where
  data := {
    family := .q45
    factId := 331
    role := 5
    anchorId := 371
    pointIds := [371,88]
    points := [p0208,p0088]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 332
    identity := "ee8c4d09f4f5084dfa03b3667b0e4c3815fda03cba0a7c4831b9d5920a1fbb43" }
  checked := by decide +kernel

theorem w0319_check : PointSegmentLeaf.check w0319.data.points
    (Quadratic3.ofRat w0319.data.radiusSquared) w0319.data.witness = true := w0319.checked

def w0320 : CheckedWitness where
  data := {
    family := .q45
    factId := 335
    role := 4
    anchorId := 370
    pointIds := [370,89]
    points := [p0100,p0089]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 336
    identity := "3ae44d4115340b81f045d4d09648822caee4904562c6a742337dd43a09863660" }
  checked := by decide +kernel

theorem w0320_check : PointSegmentLeaf.check w0320.data.points
    (Quadratic3.ofRat w0320.data.radiusSquared) w0320.data.witness = true := w0320.checked

def w0321 : CheckedWitness where
  data := {
    family := .q45
    factId := 336
    role := 5
    anchorId := 371
    pointIds := [371,89]
    points := [p0208,p0089]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 337
    identity := "12970d6fa4e0ffae5943d89402a9a0cac6eec1266ccdcf108942e1ef328c1a38" }
  checked := by decide +kernel

theorem w0321_check : PointSegmentLeaf.check w0321.data.points
    (Quadratic3.ofRat w0321.data.radiusSquared) w0321.data.witness = true := w0321.checked

def w0322 : CheckedWitness where
  data := {
    family := .q45
    factId := 340
    role := 4
    anchorId := 370
    pointIds := [370,90]
    points := [p0100,p0090]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 341
    identity := "c5bfdad013503b7ab9faf7a5b791c5587844e26a1f4d1f90b8cce8d6a0007268" }
  checked := by decide +kernel

theorem w0322_check : PointSegmentLeaf.check w0322.data.points
    (Quadratic3.ofRat w0322.data.radiusSquared) w0322.data.witness = true := w0322.checked

def w0323 : CheckedWitness where
  data := {
    family := .q45
    factId := 344
    role := 4
    anchorId := 370
    pointIds := [370,91]
    points := [p0100,p0091]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 345
    identity := "46ba99e0908942298788f58d81d9df0d7f1367d2f79cdf2ccbf8e3610d4b0650" }
  checked := by decide +kernel

theorem w0323_check : PointSegmentLeaf.check w0323.data.points
    (Quadratic3.ofRat w0323.data.radiusSquared) w0323.data.witness = true := w0323.checked

def w0324 : CheckedWitness where
  data := {
    family := .q45
    factId := 391
    role := 4
    anchorId := 370
    pointIds := [370,105]
    points := [p0100,p0105]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 392
    identity := "9589e0441192d8b8ec676270e62bbf948b3c7aa7b8f56a53ba4be699d46c1a5b" }
  checked := by decide +kernel

theorem w0324_check : PointSegmentLeaf.check w0324.data.points
    (Quadratic3.ofRat w0324.data.radiusSquared) w0324.data.witness = true := w0324.checked

def w0325 : CheckedWitness where
  data := {
    family := .q45
    factId := 392
    role := 5
    anchorId := 371
    pointIds := [371,105]
    points := [p0208,p0105]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 393
    identity := "35dcaadf23e59ad8799c4fe9cf32f6563478e8c71b0583db61e9633f946fffb3" }
  checked := by decide +kernel

theorem w0325_check : PointSegmentLeaf.check w0325.data.points
    (Quadratic3.ofRat w0325.data.radiusSquared) w0325.data.witness = true := w0325.checked

def w0326 : CheckedWitness where
  data := {
    family := .q45
    factId := 396
    role := 4
    anchorId := 370
    pointIds := [370,106]
    points := [p0100,p0106]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 397
    identity := "52545b9cb4ddc52a72cbfdc32af5aa4f4832b6c7fdb7c6c4f2e77b2e7bcbd4da" }
  checked := by decide +kernel

theorem w0326_check : PointSegmentLeaf.check w0326.data.points
    (Quadratic3.ofRat w0326.data.radiusSquared) w0326.data.witness = true := w0326.checked

def w0327 : CheckedWitness where
  data := {
    family := .q45
    factId := 397
    role := 5
    anchorId := 371
    pointIds := [371,106]
    points := [p0208,p0106]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 398
    identity := "8a683adfeff4b3a55a32311d8a39d8c571a3839b3a53445ab66f3d035b5a3a9c" }
  checked := by decide +kernel

theorem w0327_check : PointSegmentLeaf.check w0327.data.points
    (Quadratic3.ofRat w0327.data.radiusSquared) w0327.data.witness = true := w0327.checked

def w0328 : CheckedWitness where
  data := {
    family := .q45
    factId := 401
    role := 4
    anchorId := 370
    pointIds := [370,107]
    points := [p0100,p0107]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 402
    identity := "1479043e94946a26561b5b6e8b0411819f725dd5fb3065106334ba86a7ffb3b1" }
  checked := by decide +kernel

theorem w0328_check : PointSegmentLeaf.check w0328.data.points
    (Quadratic3.ofRat w0328.data.radiusSquared) w0328.data.witness = true := w0328.checked

def w0329 : CheckedWitness where
  data := {
    family := .q45
    factId := 402
    role := 5
    anchorId := 371
    pointIds := [371,107]
    points := [p0208,p0107]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 403
    identity := "303de4e0b1359c93e5bd3f3c9ce439dbb29861e089f75b5040c8a6365ef3f501" }
  checked := by decide +kernel

theorem w0329_check : PointSegmentLeaf.check w0329.data.points
    (Quadratic3.ofRat w0329.data.radiusSquared) w0329.data.witness = true := w0329.checked

def w0330 : CheckedWitness where
  data := {
    family := .q45
    factId := 403
    role := 4
    anchorId := 370
    pointIds := [370,108]
    points := [p0100,p0108]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 404
    identity := "62375807961ac178e17dcd9c8d97cccee891fdf84bb0535cd5b1e291be72b940" }
  checked := by decide +kernel

theorem w0330_check : PointSegmentLeaf.check w0330.data.points
    (Quadratic3.ofRat w0330.data.radiusSquared) w0330.data.witness = true := w0330.checked

def w0331 : CheckedWitness where
  data := {
    family := .q45
    factId := 404
    role := 5
    anchorId := 371
    pointIds := [371,108]
    points := [p0208,p0108]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 405
    identity := "80a7aab7ba62038e39e98b1cf8962a094b6eadf62f90bcedb8a6bd275c20a585" }
  checked := by decide +kernel

theorem w0331_check : PointSegmentLeaf.check w0331.data.points
    (Quadratic3.ofRat w0331.data.radiusSquared) w0331.data.witness = true := w0331.checked

def w0332 : CheckedWitness where
  data := {
    family := .q45
    factId := 446
    role := 4
    anchorId := 370
    pointIds := [370,121]
    points := [p0100,p0121]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 447
    identity := "703c34b7c9fcea4d4157c6652597eca675f098a0240ebb37a401a3b76183ce6c" }
  checked := by decide +kernel

theorem w0332_check : PointSegmentLeaf.check w0332.data.points
    (Quadratic3.ofRat w0332.data.radiusSquared) w0332.data.witness = true := w0332.checked

def w0333 : CheckedWitness where
  data := {
    family := .q45
    factId := 447
    role := 5
    anchorId := 371
    pointIds := [371,121]
    points := [p0208,p0121]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 448
    identity := "6bf37879e160011429b56bc728a6e415dd3b120872b3d02287965388bfcf2576" }
  checked := by decide +kernel

theorem w0333_check : PointSegmentLeaf.check w0333.data.points
    (Quadratic3.ofRat w0333.data.radiusSquared) w0333.data.witness = true := w0333.checked

def w0334 : CheckedWitness where
  data := {
    family := .q45
    factId := 451
    role := 4
    anchorId := 370
    pointIds := [370,122]
    points := [p0100,p0122]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 452
    identity := "fdc11eff8f3b8c836a906c2549953da935cada28275ed49216e45098a0608ea0" }
  checked := by decide +kernel

theorem w0334_check : PointSegmentLeaf.check w0334.data.points
    (Quadratic3.ofRat w0334.data.radiusSquared) w0334.data.witness = true := w0334.checked

def w0335 : CheckedWitness where
  data := {
    family := .q45
    factId := 452
    role := 5
    anchorId := 371
    pointIds := [371,122]
    points := [p0208,p0122]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 453
    identity := "8836dc24efc93bac9527d4a5a08a62e61f97cd6ae2a5c555eaed73b48317e894" }
  checked := by decide +kernel

theorem w0335_check : PointSegmentLeaf.check w0335.data.points
    (Quadratic3.ofRat w0335.data.radiusSquared) w0335.data.witness = true := w0335.checked

def w0336 : CheckedWitness where
  data := {
    family := .q45
    factId := 457
    role := 4
    anchorId := 370
    pointIds := [370,123]
    points := [p0100,p0123]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 458
    identity := "23b1f1acf79e332e15f1befaa6fabdb01a2483b8f3a4d20aa91b6e208ba2924e" }
  checked := by decide +kernel

theorem w0336_check : PointSegmentLeaf.check w0336.data.points
    (Quadratic3.ofRat w0336.data.radiusSquared) w0336.data.witness = true := w0336.checked

def w0337 : CheckedWitness where
  data := {
    family := .q45
    factId := 458
    role := 5
    anchorId := 371
    pointIds := [371,123]
    points := [p0208,p0123]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 459
    identity := "91896fd205380fe845642788e68c10627261f39135bc26d1a784623426814cbf" }
  checked := by decide +kernel

theorem w0337_check : PointSegmentLeaf.check w0337.data.points
    (Quadratic3.ofRat w0337.data.radiusSquared) w0337.data.witness = true := w0337.checked

def w0338 : CheckedWitness where
  data := {
    family := .q45
    factId := 462
    role := 4
    anchorId := 370
    pointIds := [370,124]
    points := [p0100,p0124]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 463
    identity := "ae73fb5933041b57bd24b7793034ec5550e96001b29ee806255093f01b574bfc" }
  checked := by decide +kernel

theorem w0338_check : PointSegmentLeaf.check w0338.data.points
    (Quadratic3.ofRat w0338.data.radiusSquared) w0338.data.witness = true := w0338.checked

def w0339 : CheckedWitness where
  data := {
    family := .q45
    factId := 463
    role := 5
    anchorId := 371
    pointIds := [371,124]
    points := [p0208,p0124]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 464
    identity := "0f7a47e6c4137287847ff503d2f4ba46351498b35d7906c4057c328ea508ec6d" }
  checked := by decide +kernel

theorem w0339_check : PointSegmentLeaf.check w0339.data.points
    (Quadratic3.ofRat w0339.data.radiusSquared) w0339.data.witness = true := w0339.checked

def w0340 : CheckedWitness where
  data := {
    family := .q45
    factId := 467
    role := 5
    anchorId := 371
    pointIds := [371,125]
    points := [p0208,p0125]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 468
    identity := "f5367b7408f198420d29c8288f4a3f819eebff59a9da9478a8ede9e9dddcd1d5" }
  checked := by decide +kernel

theorem w0340_check : PointSegmentLeaf.check w0340.data.points
    (Quadratic3.ofRat w0340.data.radiusSquared) w0340.data.witness = true := w0340.checked

def w0341 : CheckedWitness where
  data := {
    family := .q45
    factId := 512
    role := 4
    anchorId := 370
    pointIds := [370,137]
    points := [p0100,p0137]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 513
    identity := "ba5cd718d4c9442c03db80c3e78c7f40a88b5ea48ed4dda4077f495fb49ade1b" }
  checked := by decide +kernel

theorem w0341_check : PointSegmentLeaf.check w0341.data.points
    (Quadratic3.ofRat w0341.data.radiusSquared) w0341.data.witness = true := w0341.checked

def w0342 : CheckedWitness where
  data := {
    family := .q45
    factId := 513
    role := 5
    anchorId := 371
    pointIds := [371,137]
    points := [p0208,p0137]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 514
    identity := "f6a575cfbb99946adb8d8c2de88b31bee83e4b668a45d87054e35f2860e93ace" }
  checked := by decide +kernel

theorem w0342_check : PointSegmentLeaf.check w0342.data.points
    (Quadratic3.ofRat w0342.data.radiusSquared) w0342.data.witness = true := w0342.checked

def w0343 : CheckedWitness where
  data := {
    family := .q45
    factId := 517
    role := 4
    anchorId := 370
    pointIds := [370,138]
    points := [p0100,p0138]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 518
    identity := "4fce9c0263a3ecbee35b577416a1a697125b60ab975d916dad87e8dcb550dcc3" }
  checked := by decide +kernel

theorem w0343_check : PointSegmentLeaf.check w0343.data.points
    (Quadratic3.ofRat w0343.data.radiusSquared) w0343.data.witness = true := w0343.checked

def w0344 : CheckedWitness where
  data := {
    family := .q45
    factId := 518
    role := 5
    anchorId := 371
    pointIds := [371,138]
    points := [p0208,p0138]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 519
    identity := "a01115fa2a631d365b5f9f8ce7367212abf459a3cca6499f50a862847ad91ac6" }
  checked := by decide +kernel

theorem w0344_check : PointSegmentLeaf.check w0344.data.points
    (Quadratic3.ofRat w0344.data.radiusSquared) w0344.data.witness = true := w0344.checked

def w0345 : CheckedWitness where
  data := {
    family := .q45
    factId := 522
    role := 4
    anchorId := 370
    pointIds := [370,139]
    points := [p0100,p0139]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 523
    identity := "bd2ac88a257e7e7f1e556d6f7f4bc442a1438c5c99c5ba7e5532d4cd2fa064b6" }
  checked := by decide +kernel

theorem w0345_check : PointSegmentLeaf.check w0345.data.points
    (Quadratic3.ofRat w0345.data.radiusSquared) w0345.data.witness = true := w0345.checked

def w0346 : CheckedWitness where
  data := {
    family := .q45
    factId := 523
    role := 5
    anchorId := 371
    pointIds := [371,139]
    points := [p0208,p0139]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 524
    identity := "8bfecbe216b6c0d8f5635877387639b267c347af027c03082e6f02db171e454a" }
  checked := by decide +kernel

theorem w0346_check : PointSegmentLeaf.check w0346.data.points
    (Quadratic3.ofRat w0346.data.radiusSquared) w0346.data.witness = true := w0346.checked

def w0347 : CheckedWitness where
  data := {
    family := .q45
    factId := 528
    role := 5
    anchorId := 371
    pointIds := [371,140]
    points := [p0208,p0140]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 529
    identity := "c24c9d675a9cd52c7fb11dbed258b6aa7ad31dbeeff8bde8ba14091284293a9d" }
  checked := by decide +kernel

theorem w0347_check : PointSegmentLeaf.check w0347.data.points
    (Quadratic3.ofRat w0347.data.radiusSquared) w0347.data.witness = true := w0347.checked

def w0348 : CheckedWitness where
  data := {
    family := .q45
    factId := 532
    role := 5
    anchorId := 371
    pointIds := [371,141]
    points := [p0208,p0141]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 533
    identity := "560643a34efebac4911b9d5b29ddddff7ce0cf12ebf3387b8521eca2138e5ad0" }
  checked := by decide +kernel

theorem w0348_check : PointSegmentLeaf.check w0348.data.points
    (Quadratic3.ofRat w0348.data.radiusSquared) w0348.data.witness = true := w0348.checked

def w0349 : CheckedWitness where
  data := {
    family := .q45
    factId := 536
    role := 5
    anchorId := 371
    pointIds := [371,142]
    points := [p0208,p0142]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 537
    identity := "8b12cad17db0075b076e9177d09a1c27cc1135a54fd6816d3ef881c8ca488705" }
  checked := by decide +kernel

theorem w0349_check : PointSegmentLeaf.check w0349.data.points
    (Quadratic3.ofRat w0349.data.radiusSquared) w0349.data.witness = true := w0349.checked

def w0350 : CheckedWitness where
  data := {
    family := .q45
    factId := 576
    role := 4
    anchorId := 370
    pointIds := [370,152]
    points := [p0100,p0152]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 577
    identity := "345b2b6845bb0ad5f07ac1797a3a41915d7d2d6239bc5b395d47d4b4a8d23c09" }
  checked := by decide +kernel

theorem w0350_check : PointSegmentLeaf.check w0350.data.points
    (Quadratic3.ofRat w0350.data.radiusSquared) w0350.data.witness = true := w0350.checked

def w0351 : CheckedWitness where
  data := {
    family := .q45
    factId := 577
    role := 5
    anchorId := 371
    pointIds := [371,152]
    points := [p0208,p0152]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 578
    identity := "4ec6bd813f6c792daef0d68e5d587a3f4e4fbca777a47f852632975f6adc0fd2" }
  checked := by decide +kernel

theorem w0351_check : PointSegmentLeaf.check w0351.data.points
    (Quadratic3.ofRat w0351.data.radiusSquared) w0351.data.witness = true := w0351.checked

def w0352 : CheckedWitness where
  data := {
    family := .q45
    factId := 581
    role := 4
    anchorId := 370
    pointIds := [370,153]
    points := [p0100,p0153]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 582
    identity := "778312145f14d882bcbc428753626a933a5ac605eb772b076663abafd1daea40" }
  checked := by decide +kernel

theorem w0352_check : PointSegmentLeaf.check w0352.data.points
    (Quadratic3.ofRat w0352.data.radiusSquared) w0352.data.witness = true := w0352.checked

def w0353 : CheckedWitness where
  data := {
    family := .q45
    factId := 582
    role := 5
    anchorId := 371
    pointIds := [371,153]
    points := [p0208,p0153]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 583
    identity := "52972fdb9decff3715bd25137cba5bf18d658911dde2a5ab8292fb396aeeea03" }
  checked := by decide +kernel

theorem w0353_check : PointSegmentLeaf.check w0353.data.points
    (Quadratic3.ofRat w0353.data.radiusSquared) w0353.data.witness = true := w0353.checked

def w0354 : CheckedWitness where
  data := {
    family := .q45
    factId := 586
    role := 4
    anchorId := 370
    pointIds := [370,154]
    points := [p0100,p0154]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 587
    identity := "9fc7ab3c8da5285b3fb5a7a3ae1d22da3c33ed648057f6e242b24e8b8053a790" }
  checked := by decide +kernel

theorem w0354_check : PointSegmentLeaf.check w0354.data.points
    (Quadratic3.ofRat w0354.data.radiusSquared) w0354.data.witness = true := w0354.checked

def w0355 : CheckedWitness where
  data := {
    family := .q45
    factId := 587
    role := 5
    anchorId := 371
    pointIds := [371,154]
    points := [p0208,p0154]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 588
    identity := "f005926494d24fa4d11177e04d707f618116feac025e88d0e0cdbae44280e41d" }
  checked := by decide +kernel

theorem w0355_check : PointSegmentLeaf.check w0355.data.points
    (Quadratic3.ofRat w0355.data.radiusSquared) w0355.data.witness = true := w0355.checked

def w0356 : CheckedWitness where
  data := {
    family := .q45
    factId := 591
    role := 5
    anchorId := 371
    pointIds := [371,155]
    points := [p0208,p0155]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 592
    identity := "e86446cda2927af2bd5c25ec7cb1d705da63b6942745042d579ccdf041a29ff2" }
  checked := by decide +kernel

theorem w0356_check : PointSegmentLeaf.check w0356.data.points
    (Quadratic3.ofRat w0356.data.radiusSquared) w0356.data.witness = true := w0356.checked

def w0357 : CheckedWitness where
  data := {
    family := .q45
    factId := 595
    role := 5
    anchorId := 371
    pointIds := [371,156]
    points := [p0208,p0156]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 596
    identity := "92fda6c644128b1aa62fe60aae35ac89a61dfd8dc47930e0140cb9cd49b0ae02" }
  checked := by decide +kernel

theorem w0357_check : PointSegmentLeaf.check w0357.data.points
    (Quadratic3.ofRat w0357.data.radiusSquared) w0357.data.witness = true := w0357.checked

def w0358 : CheckedWitness where
  data := {
    family := .q45
    factId := 599
    role := 5
    anchorId := 371
    pointIds := [371,157]
    points := [p0208,p0157]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 600
    identity := "d7549740690435dacfb2383a55c7c5255cbfd5684204de33885f79b68568fa0a" }
  checked := by decide +kernel

theorem w0358_check : PointSegmentLeaf.check w0358.data.points
    (Quadratic3.ofRat w0358.data.radiusSquared) w0358.data.witness = true := w0358.checked

def w0359 : CheckedWitness where
  data := {
    family := .q45
    factId := 637
    role := 4
    anchorId := 370
    pointIds := [370,167]
    points := [p0100,p0167]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 638
    identity := "f27756862030e77240ce5011d9b3ddf6bfcb7820d91fe632ac9f165b92e0ff9e" }
  checked := by decide +kernel

theorem w0359_check : PointSegmentLeaf.check w0359.data.points
    (Quadratic3.ofRat w0359.data.radiusSquared) w0359.data.witness = true := w0359.checked

def w0360 : CheckedWitness where
  data := {
    family := .q45
    factId := 638
    role := 5
    anchorId := 371
    pointIds := [371,167]
    points := [p0208,p0167]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 639
    identity := "5578797a6fdee70ad166f4b56f3d8d4cee211aa90ec437b78329099941849ccc" }
  checked := by decide +kernel

theorem w0360_check : PointSegmentLeaf.check w0360.data.points
    (Quadratic3.ofRat w0360.data.radiusSquared) w0360.data.witness = true := w0360.checked

def w0361 : CheckedWitness where
  data := {
    family := .q45
    factId := 643
    role := 5
    anchorId := 371
    pointIds := [371,168]
    points := [p0208,p0168]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 644
    identity := "13b2cd143a1f1e0da29ed1c699985342e651c433dbe2f31fc8456dc946f19817" }
  checked := by decide +kernel

theorem w0361_check : PointSegmentLeaf.check w0361.data.points
    (Quadratic3.ofRat w0361.data.radiusSquared) w0361.data.witness = true := w0361.checked

def w0362 : CheckedWitness where
  data := {
    family := .q45
    factId := 647
    role := 5
    anchorId := 371
    pointIds := [371,169]
    points := [p0208,p0169]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 648
    identity := "6505d8f702de4767b13133f2c9feee33cd11c8939a71a3dda82abbc261c72452" }
  checked := by decide +kernel

theorem w0362_check : PointSegmentLeaf.check w0362.data.points
    (Quadratic3.ofRat w0362.data.radiusSquared) w0362.data.witness = true := w0362.checked

def w0363 : CheckedWitness where
  data := {
    family := .q45
    factId := 823
    role := 5
    anchorId := 371
    pointIds := [371,217]
    points := [p0208,p0217]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 824
    identity := "af753fe2d5ca1e85dcb662add3ba51de8d51fd7f168033d36b6783c559e9d6a3" }
  checked := by decide +kernel

theorem w0363_check : PointSegmentLeaf.check w0363.data.points
    (Quadratic3.ofRat w0363.data.radiusSquared) w0363.data.witness = true := w0363.checked

def w0364 : CheckedWitness where
  data := {
    family := .q45
    factId := 827
    role := 5
    anchorId := 371
    pointIds := [371,218]
    points := [p0208,p0218]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 828
    identity := "bc1ee2be5818012baf148d5fc833644c5f2ee60efff67dc725da85d1a03dd87e" }
  checked := by decide +kernel

theorem w0364_check : PointSegmentLeaf.check w0364.data.points
    (Quadratic3.ofRat w0364.data.radiusSquared) w0364.data.witness = true := w0364.checked

def w0365 : CheckedWitness where
  data := {
    family := .q45
    factId := 878
    role := 4
    anchorId := 370
    pointIds := [370,233]
    points := [p0100,p0233]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 879
    identity := "660acd237c4c832eec0bfcb4d7ab992362707dd2c752c2807f41b3cace0adfe3" }
  checked := by decide +kernel

theorem w0365_check : PointSegmentLeaf.check w0365.data.points
    (Quadratic3.ofRat w0365.data.radiusSquared) w0365.data.witness = true := w0365.checked

def w0366 : CheckedWitness where
  data := {
    family := .q45
    factId := 882
    role := 4
    anchorId := 370
    pointIds := [370,234]
    points := [p0100,p0234]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 883
    identity := "b8108e0e07e43f8ab5a986c8a93c9a6a13a6e9384404caa8777c0d2a58da7967" }
  checked := by decide +kernel

theorem w0366_check : PointSegmentLeaf.check w0366.data.points
    (Quadratic3.ofRat w0366.data.radiusSquared) w0366.data.witness = true := w0366.checked

def w0367 : CheckedWitness where
  data := {
    family := .q45
    factId := 886
    role := 4
    anchorId := 370
    pointIds := [370,235]
    points := [p0100,p0235]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 887
    identity := "3d0a695bcfc180fe6d51a4d93066b44e6663a3b827c084999cb2fcc5a8c70f8f" }
  checked := by decide +kernel

theorem w0367_check : PointSegmentLeaf.check w0367.data.points
    (Quadratic3.ofRat w0367.data.radiusSquared) w0367.data.witness = true := w0367.checked

def w0368 : CheckedWitness where
  data := {
    family := .q45
    factId := 890
    role := 4
    anchorId := 370
    pointIds := [370,236]
    points := [p0100,p0236]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 891
    identity := "f280625b3d7944cd4a4c01c15e2c70008c0740dbc900a77f86a76b5f40b9e1ad" }
  checked := by decide +kernel

theorem w0368_check : PointSegmentLeaf.check w0368.data.points
    (Quadratic3.ofRat w0368.data.radiusSquared) w0368.data.witness = true := w0368.checked

def w0369 : CheckedWitness where
  data := {
    family := .q45
    factId := 895
    role := 4
    anchorId := 370
    pointIds := [370,237]
    points := [p0100,p0237]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 896
    identity := "54aa7ec91310c43b2e28e6601d0ecb52d9d2aa088dde3d3cf165e30040fc49fc" }
  checked := by decide +kernel

theorem w0369_check : PointSegmentLeaf.check w0369.data.points
    (Quadratic3.ofRat w0369.data.radiusSquared) w0369.data.witness = true := w0369.checked

def w0370 : CheckedWitness where
  data := {
    family := .q45
    factId := 900
    role := 4
    anchorId := 370
    pointIds := [370,238]
    points := [p0100,p0238]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 901
    identity := "11a7504082d41f2b8964ce535c22dd263737cad58b5285855724ecb5527367d6" }
  checked := by decide +kernel

theorem w0370_check : PointSegmentLeaf.check w0370.data.points
    (Quadratic3.ofRat w0370.data.radiusSquared) w0370.data.witness = true := w0370.checked

def w0371 : CheckedWitness where
  data := {
    family := .q45
    factId := 905
    role := 4
    anchorId := 370
    pointIds := [370,239]
    points := [p0100,p0239]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 906
    identity := "6fb40235b7e70800bf3b46758981a702149ac6e46f3569d5228553f9f035e4d2" }
  checked := by decide +kernel

theorem w0371_check : PointSegmentLeaf.check w0371.data.points
    (Quadratic3.ofRat w0371.data.radiusSquared) w0371.data.witness = true := w0371.checked

def w0372 : CheckedWitness where
  data := {
    family := .q45
    factId := 906
    role := 5
    anchorId := 371
    pointIds := [371,239]
    points := [p0208,p0239]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 907
    identity := "47613bcf084a6943c54672f3bd24cfa7e61196348484b56a19a677da3725900d" }
  checked := by decide +kernel

theorem w0372_check : PointSegmentLeaf.check w0372.data.points
    (Quadratic3.ofRat w0372.data.radiusSquared) w0372.data.witness = true := w0372.checked

def w0373 : CheckedWitness where
  data := {
    family := .q45
    factId := 910
    role := 4
    anchorId := 370
    pointIds := [370,240]
    points := [p0100,p0240]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 911
    identity := "7dff5256427c75ae6c886510f33e359a2d165bd21a496b75b258367964ebe501" }
  checked := by decide +kernel

theorem w0373_check : PointSegmentLeaf.check w0373.data.points
    (Quadratic3.ofRat w0373.data.radiusSquared) w0373.data.witness = true := w0373.checked

def w0374 : CheckedWitness where
  data := {
    family := .q45
    factId := 911
    role := 5
    anchorId := 371
    pointIds := [371,240]
    points := [p0208,p0240]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 912
    identity := "af28b5eb74bc0468d82c60438c3491dd026a9a0fc3bcd332f5286026b4bf824c" }
  checked := by decide +kernel

theorem w0374_check : PointSegmentLeaf.check w0374.data.points
    (Quadratic3.ofRat w0374.data.radiusSquared) w0374.data.witness = true := w0374.checked

def w0375 : CheckedWitness where
  data := {
    family := .q45
    factId := 915
    role := 4
    anchorId := 370
    pointIds := [370,241]
    points := [p0100,p0241]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 916
    identity := "583158c0e1e4da05de8d6a5251d5c17c42328defb8117b246ac7d8d82f9c46bc" }
  checked := by decide +kernel

theorem w0375_check : PointSegmentLeaf.check w0375.data.points
    (Quadratic3.ofRat w0375.data.radiusSquared) w0375.data.witness = true := w0375.checked

def w0376 : CheckedWitness where
  data := {
    family := .q45
    factId := 916
    role := 5
    anchorId := 371
    pointIds := [371,241]
    points := [p0208,p0241]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 917
    identity := "223fa2271be554a0ba405f714493ef0433f805710d8bf15c1c27917bbd61974b" }
  checked := by decide +kernel

theorem w0376_check : PointSegmentLeaf.check w0376.data.points
    (Quadratic3.ofRat w0376.data.radiusSquared) w0376.data.witness = true := w0376.checked

def w0377 : CheckedWitness where
  data := {
    family := .q45
    factId := 920
    role := 4
    anchorId := 370
    pointIds := [370,242]
    points := [p0100,p0242]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 921
    identity := "57110f2cb17c1f3f029fbad8c028c0d33b3d37d982f49bab38e8fa468cc2987e" }
  checked := by decide +kernel

theorem w0377_check : PointSegmentLeaf.check w0377.data.points
    (Quadratic3.ofRat w0377.data.radiusSquared) w0377.data.witness = true := w0377.checked

def w0378 : CheckedWitness where
  data := {
    family := .q45
    factId := 921
    role := 5
    anchorId := 371
    pointIds := [371,242]
    points := [p0208,p0242]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 922
    identity := "1cd5a7a7007664e68fe3071618eca9a187ce81cbe917a010214f4bc20cbd6ae1" }
  checked := by decide +kernel

theorem w0378_check : PointSegmentLeaf.check w0378.data.points
    (Quadratic3.ofRat w0378.data.radiusSquared) w0378.data.witness = true := w0378.checked

def w0379 : CheckedWitness where
  data := {
    family := .q45
    factId := 926
    role := 4
    anchorId := 370
    pointIds := [370,243]
    points := [p0100,p0243]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 927
    identity := "efd34f20b2c1244176d950c016a1f50b9893af8e8a6cee6123bb2859cb216936" }
  checked := by decide +kernel

theorem w0379_check : PointSegmentLeaf.check w0379.data.points
    (Quadratic3.ofRat w0379.data.radiusSquared) w0379.data.witness = true := w0379.checked

def w0380 : CheckedWitness where
  data := {
    family := .q45
    factId := 927
    role := 5
    anchorId := 371
    pointIds := [371,243]
    points := [p0208,p0243]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 928
    identity := "3761c233b37d82cae06feff282843fc9b2cfe21ef08d6745677247d6d680b532" }
  checked := by decide +kernel

theorem w0380_check : PointSegmentLeaf.check w0380.data.points
    (Quadratic3.ofRat w0380.data.radiusSquared) w0380.data.witness = true := w0380.checked

def w0381 : CheckedWitness where
  data := {
    family := .q45
    factId := 932
    role := 4
    anchorId := 370
    pointIds := [370,244]
    points := [p0100,p0244]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 933
    identity := "333a472dafbda9a34c57c31219ee1942c8b866e9857fa7b4a7f5d4bf379a4dd0" }
  checked := by decide +kernel

theorem w0381_check : PointSegmentLeaf.check w0381.data.points
    (Quadratic3.ofRat w0381.data.radiusSquared) w0381.data.witness = true := w0381.checked

def w0382 : CheckedWitness where
  data := {
    family := .q45
    factId := 933
    role := 5
    anchorId := 371
    pointIds := [371,244]
    points := [p0208,p0244]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 934
    identity := "cf6527386d55b34a2863790cb4c18b49f332d7d003cd44f07a25aef2ff26fd4c" }
  checked := by decide +kernel

theorem w0382_check : PointSegmentLeaf.check w0382.data.points
    (Quadratic3.ofRat w0382.data.radiusSquared) w0382.data.witness = true := w0382.checked

def w0383 : CheckedWitness where
  data := {
    family := .q45
    factId := 937
    role := 4
    anchorId := 370
    pointIds := [370,245]
    points := [p0100,p0245]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 938
    identity := "a4dd50f678f993937b4a5a218865eb0163f732282ee33528eeced7794a83f1e0" }
  checked := by decide +kernel

theorem w0383_check : PointSegmentLeaf.check w0383.data.points
    (Quadratic3.ofRat w0383.data.radiusSquared) w0383.data.witness = true := w0383.checked

def w0384 : CheckedWitness where
  data := {
    family := .q45
    factId := 938
    role := 5
    anchorId := 371
    pointIds := [371,245]
    points := [p0208,p0245]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 939
    identity := "056d057870835f92ff950eb9f9aa87c40773beddd8f67fff2ef553cd8e30e3a1" }
  checked := by decide +kernel

theorem w0384_check : PointSegmentLeaf.check w0384.data.points
    (Quadratic3.ofRat w0384.data.radiusSquared) w0384.data.witness = true := w0384.checked

def w0385 : CheckedWitness where
  data := {
    family := .q45
    factId := 942
    role := 4
    anchorId := 370
    pointIds := [370,246]
    points := [p0100,p0246]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 943
    identity := "e6d7937b45d7faff4e52dfe746491b57fab3c19f359bd6a2e838c479a71c98a8" }
  checked := by decide +kernel

theorem w0385_check : PointSegmentLeaf.check w0385.data.points
    (Quadratic3.ofRat w0385.data.radiusSquared) w0385.data.witness = true := w0385.checked

def w0386 : CheckedWitness where
  data := {
    family := .q45
    factId := 943
    role := 5
    anchorId := 371
    pointIds := [371,246]
    points := [p0208,p0246]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 944
    identity := "15d086da36a0008b44a04b37e5067c3cd9b4cfecde298edf499b5f96f7e166e0" }
  checked := by decide +kernel

theorem w0386_check : PointSegmentLeaf.check w0386.data.points
    (Quadratic3.ofRat w0386.data.radiusSquared) w0386.data.witness = true := w0386.checked

def w0387 : CheckedWitness where
  data := {
    family := .q45
    factId := 947
    role := 4
    anchorId := 370
    pointIds := [370,247]
    points := [p0100,p0247]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 948
    identity := "a4739a77acc3622b451c02c901f04f319509d8b93a522bedbd2e6a5b118dbeb5" }
  checked := by decide +kernel

theorem w0387_check : PointSegmentLeaf.check w0387.data.points
    (Quadratic3.ofRat w0387.data.radiusSquared) w0387.data.witness = true := w0387.checked

def w0388 : CheckedWitness where
  data := {
    family := .q45
    factId := 948
    role := 5
    anchorId := 371
    pointIds := [371,247]
    points := [p0208,p0247]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 949
    identity := "b1c4af6ac139879d2e8e9a17249b3302b878636a7b014c2bd5635b62247fee92" }
  checked := by decide +kernel

theorem w0388_check : PointSegmentLeaf.check w0388.data.points
    (Quadratic3.ofRat w0388.data.radiusSquared) w0388.data.witness = true := w0388.checked

def w0389 : CheckedWitness where
  data := {
    family := .q45
    factId := 952
    role := 4
    anchorId := 370
    pointIds := [370,248]
    points := [p0100,p0248]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 953
    identity := "96c7084b7a1179aac6e534bdb77dcbfba54ebde9263db40d985d8ab64bde9750" }
  checked := by decide +kernel

theorem w0389_check : PointSegmentLeaf.check w0389.data.points
    (Quadratic3.ofRat w0389.data.radiusSquared) w0389.data.witness = true := w0389.checked

def w0390 : CheckedWitness where
  data := {
    family := .q45
    factId := 953
    role := 5
    anchorId := 371
    pointIds := [371,248]
    points := [p0208,p0248]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 954
    identity := "b0e7f779771ac5d8ac4e4210569a64a4a95e5ac42ae369bc6153d468de97e0cb" }
  checked := by decide +kernel

theorem w0390_check : PointSegmentLeaf.check w0390.data.points
    (Quadratic3.ofRat w0390.data.radiusSquared) w0390.data.witness = true := w0390.checked

def w0391 : CheckedWitness where
  data := {
    family := .q45
    factId := 958
    role := 5
    anchorId := 371
    pointIds := [371,249]
    points := [p0208,p0249]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 959
    identity := "51300148e67a775c9088e34e0ff132668fcbc114afa63a8e6b786d07eb6167fe" }
  checked := by decide +kernel

theorem w0391_check : PointSegmentLeaf.check w0391.data.points
    (Quadratic3.ofRat w0391.data.radiusSquared) w0391.data.witness = true := w0391.checked

def w0392 : CheckedWitness where
  data := {
    family := .q45
    factId := 963
    role := 5
    anchorId := 371
    pointIds := [371,250]
    points := [p0208,p0250]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 964
    identity := "ff4f7a86915cc30ecf359e52a1236a281de1fac0447225dfc6eb7dbd5b76dd4d" }
  checked := by decide +kernel

theorem w0392_check : PointSegmentLeaf.check w0392.data.points
    (Quadratic3.ofRat w0392.data.radiusSquared) w0392.data.witness = true := w0392.checked

def w0393 : CheckedWitness where
  data := {
    family := .q45
    factId := 967
    role := 5
    anchorId := 371
    pointIds := [371,251]
    points := [p0208,p0251]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 968
    identity := "b81ae23efdfe266cdacfc9eae4d74f567f434ff17ab2da8187167cefcf3ec162" }
  checked := by decide +kernel

theorem w0393_check : PointSegmentLeaf.check w0393.data.points
    (Quadratic3.ofRat w0393.data.radiusSquared) w0393.data.witness = true := w0393.checked

def w0394 : CheckedWitness where
  data := {
    family := .q45
    factId := 971
    role := 5
    anchorId := 371
    pointIds := [371,252]
    points := [p0208,p0252]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 972
    identity := "1aaaa2c1f108ce330f38197313bd51aee9c513ba37661648b3d6b4e36d83ca8f" }
  checked := by decide +kernel

theorem w0394_check : PointSegmentLeaf.check w0394.data.points
    (Quadratic3.ofRat w0394.data.radiusSquared) w0394.data.witness = true := w0394.checked

def w0395 : CheckedWitness where
  data := {
    family := .q45
    factId := 1065
    role := 4
    anchorId := 370
    pointIds := [370,280]
    points := [p0100,p0280]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1066
    identity := "7c549acc23f8b6a2b81c58e36ff2c208561a6ba8011617c4d23a6b6c25fbb16e" }
  checked := by decide +kernel

theorem w0395_check : PointSegmentLeaf.check w0395.data.points
    (Quadratic3.ofRat w0395.data.radiusSquared) w0395.data.witness = true := w0395.checked

def w0396 : CheckedWitness where
  data := {
    family := .q45
    factId := 1066
    role := 5
    anchorId := 371
    pointIds := [371,280]
    points := [p0208,p0280]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1067
    identity := "b48f58fcc73ac6adfcab23afb5d635edab04ada149db1138d658d2d435ede41c" }
  checked := by decide +kernel

theorem w0396_check : PointSegmentLeaf.check w0396.data.points
    (Quadratic3.ofRat w0396.data.radiusSquared) w0396.data.witness = true := w0396.checked

def w0397 : CheckedWitness where
  data := {
    family := .q45
    factId := 1078
    role := 5
    anchorId := 371
    pointIds := [371,284]
    points := [p0208,p0284]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1079
    identity := "26676bdcb8477a3b14dd5e4792b71209f5882bbcaf8af118056ca6b9f2d39586" }
  checked := by decide +kernel

theorem w0397_check : PointSegmentLeaf.check w0397.data.points
    (Quadratic3.ofRat w0397.data.radiusSquared) w0397.data.witness = true := w0397.checked

def w0398 : CheckedWitness where
  data := {
    family := .q45
    factId := 1106
    role := 5
    anchorId := 371
    pointIds := [371,291]
    points := [p0208,p0291]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1107
    identity := "621d21a0fb49e44b44c18566a16f5fbcb28380f13b7736b9be3913f5710d8668" }
  checked := by decide +kernel

theorem w0398_check : PointSegmentLeaf.check w0398.data.points
    (Quadratic3.ofRat w0398.data.radiusSquared) w0398.data.witness = true := w0398.checked

def w0399 : CheckedWitness where
  data := {
    family := .q45
    factId := 1111
    role := 5
    anchorId := 371
    pointIds := [371,292]
    points := [p0208,p0292]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1112
    identity := "fae69baf2811f94d3377c044510d8f4971f7270b2853dc148cba5d82d481dbd2" }
  checked := by decide +kernel

theorem w0399_check : PointSegmentLeaf.check w0399.data.points
    (Quadratic3.ofRat w0399.data.radiusSquared) w0399.data.witness = true := w0399.checked

def w0400 : CheckedWitness where
  data := {
    family := .q45
    factId := 1178
    role := 5
    anchorId := 371
    pointIds := [371,309]
    points := [p0208,p0309]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1179
    identity := "e0768359e23fdf0c4ec2dbe225e92235059d97bbb102bc5a13544faa5fd462c6" }
  checked := by decide +kernel

theorem w0400_check : PointSegmentLeaf.check w0400.data.points
    (Quadratic3.ofRat w0400.data.radiusSquared) w0400.data.witness = true := w0400.checked

def w0401 : CheckedWitness where
  data := {
    family := .q45
    factId := 1190
    role := 5
    anchorId := 371
    pointIds := [371,312]
    points := [p0208,p0312]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1191
    identity := "ade5aaaa942705b6629ff83ce836f20283eb7a8526f8f3960e4f6500d0ac7904" }
  checked := by decide +kernel

theorem w0401_check : PointSegmentLeaf.check w0401.data.points
    (Quadratic3.ofRat w0401.data.radiusSquared) w0401.data.witness = true := w0401.checked

def w0402 : CheckedWitness where
  data := {
    family := .q45
    factId := 1194
    role := 5
    anchorId := 371
    pointIds := [371,313]
    points := [p0208,p0313]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1195
    identity := "c432b21284298b524f198a1f6440f465cef1aece9c7b7ad4dd3bee0386621c9d" }
  checked := by decide +kernel

theorem w0402_check : PointSegmentLeaf.check w0402.data.points
    (Quadratic3.ofRat w0402.data.radiusSquared) w0402.data.witness = true := w0402.checked

def w0403 : CheckedWitness where
  data := {
    family := .q45
    factId := 1214
    role := 5
    anchorId := 371
    pointIds := [371,318]
    points := [p0208,p0317]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1215
    identity := "71bb1f20d5a5802d25d709b191729b951adb2d8053b530906492f925df53bdb6" }
  checked := by decide +kernel

theorem w0403_check : PointSegmentLeaf.check w0403.data.points
    (Quadratic3.ofRat w0403.data.radiusSquared) w0403.data.witness = true := w0403.checked

def w0404 : CheckedWitness where
  data := {
    family := .q45
    factId := 1218
    role := 5
    anchorId := 371
    pointIds := [371,319]
    points := [p0208,p0318]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1219
    identity := "436cc7a54a38682e6716a459136fb666e07d64ac6d00370c3b61edb5c085cfa8" }
  checked := by decide +kernel

theorem w0404_check : PointSegmentLeaf.check w0404.data.points
    (Quadratic3.ofRat w0404.data.radiusSquared) w0404.data.witness = true := w0404.checked

def w0405 : CheckedWitness where
  data := {
    family := .q45
    factId := 1229
    role := 4
    anchorId := 370
    pointIds := [370,323]
    points := [p0100,p0321]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1230
    identity := "dd66f569abd751145ce8b0212e8a672aabd5c8af440c771f5401e45f523dc69a" }
  checked := by decide +kernel

theorem w0405_check : PointSegmentLeaf.check w0405.data.points
    (Quadratic3.ofRat w0405.data.radiusSquared) w0405.data.witness = true := w0405.checked

def w0406 : CheckedWitness where
  data := {
    family := .q45
    factId := 1257
    role := 5
    anchorId := 371
    pointIds := [371,331]
    points := [p0208,p0328]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1258
    identity := "b7fe895804ce1aa3458b4f62d26a629a89211b92f0d80a8fbe1d638f66d09e4c" }
  checked := by decide +kernel

theorem w0406_check : PointSegmentLeaf.check w0406.data.points
    (Quadratic3.ofRat w0406.data.radiusSquared) w0406.data.witness = true := w0406.checked

def w0407 : CheckedWitness where
  data := {
    family := .q45
    factId := 1268
    role := 4
    anchorId := 370
    pointIds := [370,334]
    points := [p0100,p0331]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1269
    identity := "b4e2c8f3fb6315f22b0be78787af404b26465cb478821e3c72cbf38df8545134" }
  checked := by decide +kernel

theorem w0407_check : PointSegmentLeaf.check w0407.data.points
    (Quadratic3.ofRat w0407.data.radiusSquared) w0407.data.witness = true := w0407.checked

def w0408 : CheckedWitness where
  data := {
    family := .q45
    factId := 1301
    role := 4
    anchorId := 370
    pointIds := [370,342]
    points := [p0100,p0339]
    radiusSquared := 1/4
    witness := .point 1
    originalFlag := true
    sourceNI := true
    journalLine := 1302
    identity := "89c47d999a365df0cf2a53762571c3fe3c42ae8237cabf83e29892aed05bc4a9" }
  checked := by decide +kernel

theorem w0408_check : PointSegmentLeaf.check w0408.data.points
    (Quadratic3.ofRat w0408.data.radiusSquared) w0408.data.witness = true := w0408.checked

def w0409 : CheckedWitness where
  data := {
    family := .q45
    factId := 1659
    role := 4
    anchorId := 370
    pointIds := [370,46,117,133]
    points := [p0100,p0046,p0117,p0133]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 1660
    identity := "7abcf43b4130e8f62161e4b602b44e0803c725438fce49db80a4df85d1e26f7d" }
  checked := by decide +kernel

theorem w0409_check : PointSegmentLeaf.check w0409.data.points
    (Quadratic3.ofRat w0409.data.radiusSquared) w0409.data.witness = true := w0409.checked

def w0410 : CheckedWitness where
  data := {
    family := .q45
    factId := 2170
    role := 4
    anchorId := 370
    pointIds := [370,46,100,117,133]
    points := [p0100,p0046,p0100,p0117,p0133]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 2171
    identity := "1132f08b7647922f36c4a2d7f416d7af799cd31a50020b7022ec22a74d8d22ac" }
  checked := by decide +kernel

theorem w0410_check : PointSegmentLeaf.check w0410.data.points
    (Quadratic3.ofRat w0410.data.radiusSquared) w0410.data.witness = true := w0410.checked

def w0411 : CheckedWitness where
  data := {
    family := .q45
    factId := 3168
    role := 5
    anchorId := 371
    pointIds := [371,204,208,209,210,212,213,214,261,269,279,299,300,308,345,346,355,365]
    points := [p0208,p0204,p0208,p0209,p0210,p0212,p0213,p0214,p0261,p0269,p0279,p0299,p0300,p0308,p0342,p0343,p0352,p0362]
    radiusSquared := 1/4
    witness := .segment 12 17
    originalFlag := false
    sourceNI := true
    journalLine := 3169
    identity := "6ca529f6ff1d242fbeff4c273abba41737eba80f5e27c68ad57b90448dbc723d" }
  checked := by decide +kernel

theorem w0411_check : PointSegmentLeaf.check w0411.data.points
    (Quadratic3.ofRat w0411.data.radiusSquared) w0411.data.witness = true := w0411.checked

def w0412 : CheckedWitness where
  data := {
    family := .q45
    factId := 3171
    role := 4
    anchorId := 370
    pointIds := [370,100,101,104,117,133,162,163,175,177,278,297,326]
    points := [p0100,p0100,p0101,p0104,p0117,p0133,p0162,p0163,p0175,p0177,p0278,p0297,p0323]
    radiusSquared := 1/4
    witness := .segment 3 9
    originalFlag := false
    sourceNI := true
    journalLine := 3172
    identity := "9b837bec56effbf6a0c0793024ac35a4688231aff8d53696e2ed2afaf3591425" }
  checked := by decide +kernel

theorem w0412_check : PointSegmentLeaf.check w0412.data.points
    (Quadratic3.ofRat w0412.data.radiusSquared) w0412.data.witness = true := w0412.checked

def w0413 : CheckedWitness where
  data := {
    family := .q45
    factId := 3368
    role := 4
    anchorId := 370
    pointIds := [370,46,100,101,117,133]
    points := [p0100,p0046,p0100,p0101,p0117,p0133]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 3369
    identity := "177a723cd7d9c776168b956a7c31e01bca766a2225cddbc7b20a0305fff2f6dc" }
  checked := by decide +kernel

theorem w0413_check : PointSegmentLeaf.check w0413.data.points
    (Quadratic3.ofRat w0413.data.radiusSquared) w0413.data.witness = true := w0413.checked

def w0414 : CheckedWitness where
  data := {
    family := .q45
    factId := 3492
    role := 5
    anchorId := 371
    pointIds := [371,193,204,208,209,210,212,213,214,261,269,279,299,300,308,345,346,355]
    points := [p0208,p0193,p0204,p0208,p0209,p0210,p0212,p0213,p0214,p0261,p0269,p0279,p0299,p0300,p0308,p0342,p0343,p0352]
    radiusSquared := 1/4
    witness := .segment 1 13
    originalFlag := false
    sourceNI := true
    journalLine := 3493
    identity := "02899f85599729e9f3683e3c8d1fdad11733a53f83aa9c57c3f195e1beee31de" }
  checked := by decide +kernel

theorem w0414_check : PointSegmentLeaf.check w0414.data.points
    (Quadratic3.ofRat w0414.data.radiusSquared) w0414.data.witness = true := w0414.checked

def w0415 : CheckedWitness where
  data := {
    family := .q45
    factId := 3495
    role := 4
    anchorId := 370
    pointIds := [370,100,101,104,117,133,148,149,162,163,164,175,176,177,278,297]
    points := [p0100,p0100,p0101,p0104,p0117,p0133,p0148,p0149,p0162,p0163,p0164,p0175,p0176,p0177,p0278,p0297]
    radiusSquared := 1/4
    witness := .segment 3 13
    originalFlag := false
    sourceNI := true
    journalLine := 3496
    identity := "6b6c3c254cd4ceaa925dc8df82f09d6641e467af72181de1e78813f9bc0591f5" }
  checked := by decide +kernel

theorem w0415_check : PointSegmentLeaf.check w0415.data.points
    (Quadratic3.ofRat w0415.data.radiusSquared) w0415.data.witness = true := w0415.checked

def w0416 : CheckedWitness where
  data := {
    family := .q45
    factId := 3583
    role := 4
    anchorId := 370
    pointIds := [370,84,100,101,104,117,133,175,176,177,278,297]
    points := [p0100,p0084,p0100,p0101,p0104,p0117,p0133,p0175,p0176,p0177,p0278,p0297]
    radiusSquared := 1/4
    witness := .segment 4 9
    originalFlag := false
    sourceNI := true
    journalLine := 3584
    identity := "50174b9399c2d43064307d081180671e43c02474b76e30194d1ecafdbb1c677b" }
  checked := by decide +kernel

theorem w0416_check : PointSegmentLeaf.check w0416.data.points
    (Quadratic3.ofRat w0416.data.radiusSquared) w0416.data.witness = true := w0416.checked

def w0417 : CheckedWitness where
  data := {
    family := .q45
    factId := 3663
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,101,117,133,166,278,297]
    points := [p0100,p0069,p0084,p0100,p0101,p0117,p0133,p0166,p0278,p0297]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 3664
    identity := "4055cf72784f215d7bd1e33a287baff851a25ddc08706f7194dd8ebe86307e45" }
  checked := by decide +kernel

theorem w0417_check : PointSegmentLeaf.check w0417.data.points
    (Quadratic3.ofRat w0417.data.radiusSquared) w0417.data.witness = true := w0417.checked

def w0418 : CheckedWitness where
  data := {
    family := .q45
    factId := 3855
    role := 4
    anchorId := 370
    pointIds := [370,46,100,117,133,297]
    points := [p0100,p0046,p0100,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 3856
    identity := "41a3df059e1f0454bb946cb0fee1830a034ecb4700cf94dc39cd229c6469ea76" }
  checked := by decide +kernel

theorem w0418_check : PointSegmentLeaf.check w0418.data.points
    (Quadratic3.ofRat w0418.data.radiusSquared) w0418.data.witness = true := w0418.checked

def w0419 : CheckedWitness where
  data := {
    family := .q45
    factId := 3931
    role := 4
    anchorId := 370
    pointIds := [370,100,101,102,104,117,118,133,148,175,176,177,297]
    points := [p0100,p0100,p0101,p0102,p0104,p0117,p0118,p0133,p0148,p0175,p0176,p0177,p0297]
    radiusSquared := 1/4
    witness := .segment 4 11
    originalFlag := false
    sourceNI := true
    journalLine := 3932
    identity := "31727ac34a5ac171d81bb992657be792f78a138a4aae835436fe83e0613dc050" }
  checked := by decide +kernel

theorem w0419_check : PointSegmentLeaf.check w0419.data.points
    (Quadratic3.ofRat w0419.data.radiusSquared) w0419.data.witness = true := w0419.checked

def w0420 : CheckedWitness where
  data := {
    family := .q45
    factId := 4167
    role := 4
    anchorId := 370
    pointIds := [370,100,101,104,117,133,148,149,162,163,164,175,176,177,297,326]
    points := [p0100,p0100,p0101,p0104,p0117,p0133,p0148,p0149,p0162,p0163,p0164,p0175,p0176,p0177,p0297,p0323]
    radiusSquared := 1/4
    witness := .segment 3 13
    originalFlag := false
    sourceNI := true
    journalLine := 4168
    identity := "8856f04977ec20da41b4e9c97732e9f9419f92c841037d9b984f9a2a925dc224" }
  checked := by decide +kernel

theorem w0420_check : PointSegmentLeaf.check w0420.data.points
    (Quadratic3.ofRat w0420.data.radiusSquared) w0420.data.witness = true := w0420.checked

def w0421 : CheckedWitness where
  data := {
    family := .q45
    factId := 4554
    role := 4
    anchorId := 370
    pointIds := [370,100,101,104,117,133,148,149,162,163,164,175,176,177,278,297,326]
    points := [p0100,p0100,p0101,p0104,p0117,p0133,p0148,p0149,p0162,p0163,p0164,p0175,p0176,p0177,p0278,p0297,p0323]
    radiusSquared := 1/4
    witness := .segment 3 13
    originalFlag := false
    sourceNI := true
    journalLine := 4555
    identity := "7d6ac172ce922d3800d7dfaac09591748831780107f77380af22c7dfeb406be7" }
  checked := by decide +kernel

theorem w0421_check : PointSegmentLeaf.check w0421.data.points
    (Quadratic3.ofRat w0421.data.radiusSquared) w0421.data.witness = true := w0421.checked

def w0422 : CheckedWitness where
  data := {
    family := .q45
    factId := 4698
    role := 5
    anchorId := 371
    pointIds := [371,136,204,208,209,212,213,261,269,279,299,308,345,346]
    points := [p0208,p0136,p0204,p0208,p0209,p0212,p0213,p0261,p0269,p0279,p0299,p0308,p0342,p0343]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 4699
    identity := "50de259895e39770ae1e0c36f8b4f11260ac8c94d645c30042f17009c7b0c65b" }
  checked := by decide +kernel

theorem w0422_check : PointSegmentLeaf.check w0422.data.points
    (Quadratic3.ofRat w0422.data.radiusSquared) w0422.data.witness = true := w0422.checked

def w0423 : CheckedWitness where
  data := {
    family := .q45
    factId := 4751
    role := 4
    anchorId := 370
    pointIds := [370,100,101,104,117,133,148,149,162,163,164,175,176,177,297]
    points := [p0100,p0100,p0101,p0104,p0117,p0133,p0148,p0149,p0162,p0163,p0164,p0175,p0176,p0177,p0297]
    radiusSquared := 1/4
    witness := .segment 3 13
    originalFlag := false
    sourceNI := true
    journalLine := 4752
    identity := "17038b9271a6333aa3538082619c43b92194ceeffe6a34b988c3d5f4de8176fa" }
  checked := by decide +kernel

theorem w0423_check : PointSegmentLeaf.check w0423.data.points
    (Quadratic3.ofRat w0423.data.radiusSquared) w0423.data.witness = true := w0423.checked

def w0424 : CheckedWitness where
  data := {
    family := .q45
    factId := 4958
    role := 4
    anchorId := 370
    pointIds := [370,84,85,100,101,117,166,297]
    points := [p0100,p0084,p0085,p0100,p0101,p0117,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 4959
    identity := "8e533d030233fb184a0000093bceddd4a82f809e6a45de9ca9c2a1521d43c528" }
  checked := by decide +kernel

theorem w0424_check : PointSegmentLeaf.check w0424.data.points
    (Quadratic3.ofRat w0424.data.radiusSquared) w0424.data.witness = true := w0424.checked

def w0425 : CheckedWitness where
  data := {
    family := .q45
    factId := 4969
    role := 4
    anchorId := 370
    pointIds := [370,46,84,85,100,101,117,162,297]
    points := [p0100,p0046,p0084,p0085,p0100,p0101,p0117,p0162,p0297]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 4970
    identity := "3ddb7c7a18f5c369da3f7b90561c8b8181c3c6c068c34aab5021d6bfb045f183" }
  checked := by decide +kernel

theorem w0425_check : PointSegmentLeaf.check w0425.data.points
    (Quadratic3.ofRat w0425.data.radiusSquared) w0425.data.witness = true := w0425.checked

def w0426 : CheckedWitness where
  data := {
    family := .q45
    factId := 5013
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,101,117,166,297]
    points := [p0100,p0069,p0084,p0100,p0101,p0117,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 5014
    identity := "81344badfc5167fa7da1e6fca6aba0ea5007097b5e0577cc463163b4846e9d33" }
  checked := by decide +kernel

theorem w0426_check : PointSegmentLeaf.check w0426.data.points
    (Quadratic3.ofRat w0426.data.radiusSquared) w0426.data.witness = true := w0426.checked

def w0427 : CheckedWitness where
  data := {
    family := .q45
    factId := 5082
    role := 4
    anchorId := 370
    pointIds := [370,46,69,84,85,100,101,117,133,297]
    points := [p0100,p0046,p0069,p0084,p0085,p0100,p0101,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 5083
    identity := "ee5ecf8df037a67fe61a579984d5c3913f7d54a3c2d62b11309fca4228b4e988" }
  checked := by decide +kernel

theorem w0427_check : PointSegmentLeaf.check w0427.data.points
    (Quadratic3.ofRat w0427.data.radiusSquared) w0427.data.witness = true := w0427.checked

def w0428 : CheckedWitness where
  data := {
    family := .q45
    factId := 5339
    role := 5
    anchorId := 371
    pointIds := [371,166,181,198,199,204,208,209,212,213,214,261,269,279,299,308,345]
    points := [p0208,p0166,p0181,p0198,p0199,p0204,p0208,p0209,p0212,p0213,p0214,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 5340
    identity := "29b7270582da98f9d969862410d56b6a28a63db3b1b456453256d64f40d0bd0f" }
  checked := by decide +kernel

theorem w0428_check : PointSegmentLeaf.check w0428.data.points
    (Quadratic3.ofRat w0428.data.radiusSquared) w0428.data.witness = true := w0428.checked

def w0429 : CheckedWitness where
  data := {
    family := .q45
    factId := 5477
    role := 4
    anchorId := 370
    pointIds := [370,30,84,100,101,117,297,328]
    points := [p0100,p0030,p0084,p0100,p0101,p0117,p0297,p0325]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 5478
    identity := "80f756ac7a8381d6451ab2ada9390bfcf5141770df88fb1a6cebe394e0591705" }
  checked := by decide +kernel

theorem w0429_check : PointSegmentLeaf.check w0429.data.points
    (Quadratic3.ofRat w0429.data.radiusSquared) w0429.data.witness = true := w0429.checked

def w0430 : CheckedWitness where
  data := {
    family := .q45
    factId := 5510
    role := 4
    anchorId := 370
    pointIds := [370,55,84,100,101,117,166,297]
    points := [p0100,p0055,p0084,p0100,p0101,p0117,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 5511
    identity := "dbd29f54070a99e65dd36914768bb1374db7c319eb9c3c68d17e2ed191fba45c" }
  checked := by decide +kernel

theorem w0430_check : PointSegmentLeaf.check w0430.data.points
    (Quadratic3.ofRat w0430.data.radiusSquared) w0430.data.witness = true := w0430.checked

def w0431 : CheckedWitness where
  data := {
    family := .q45
    factId := 6120
    role := 5
    anchorId := 371
    pointIds := [371,104,198,208,209,261,269,279,299,308,345]
    points := [p0208,p0104,p0198,p0208,p0209,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 6121
    identity := "3c77d372f9b7296ae0bafc7829544ae4599b45e4de212104e8b3f5b9e9681444" }
  checked := by decide +kernel

theorem w0431_check : PointSegmentLeaf.check w0431.data.points
    (Quadratic3.ofRat w0431.data.radiusSquared) w0431.data.witness = true := w0431.checked

def w0432 : CheckedWitness where
  data := {
    family := .q45
    factId := 6263
    role := 4
    anchorId := 370
    pointIds := [370,84,85,100,101,117,118,133,134,148,149,162,166,297]
    points := [p0100,p0084,p0085,p0100,p0101,p0117,p0118,p0133,p0134,p0148,p0149,p0162,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 12
    originalFlag := false
    sourceNI := true
    journalLine := 6264
    identity := "f1295f63966d4ef3b103580940305a6a2304c0c741331cc8efa995475128b2a9" }
  checked := by decide +kernel

theorem w0432_check : PointSegmentLeaf.check w0432.data.points
    (Quadratic3.ofRat w0432.data.radiusSquared) w0432.data.witness = true := w0432.checked

def w0433 : CheckedWitness where
  data := {
    family := .q45
    factId := 6290
    role := 5
    anchorId := 371
    pointIds := [371,136,198,199,200,202,203,208,209,210,211,212,213,261,269,279,287,299,308,337,345]
    points := [p0208,p0136,p0198,p0199,p0200,p0202,p0203,p0208,p0209,p0210,p0211,p0212,p0213,p0261,p0269,p0279,p0287,p0299,p0308,p0334,p0342]
    radiusSquared := 1/4
    witness := .segment 1 19
    originalFlag := false
    sourceNI := true
    journalLine := 6291
    identity := "0c37e223b72da3ad0d6683f7be456e16deaf64ee7e0f5786314bdcde269e18d5" }
  checked := by decide +kernel

theorem w0433_check : PointSegmentLeaf.check w0433.data.points
    (Quadratic3.ofRat w0433.data.radiusSquared) w0433.data.witness = true := w0433.checked

def w0434 : CheckedWitness where
  data := {
    family := .q45
    factId := 6379
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,117,166,297]
    points := [p0100,p0069,p0084,p0100,p0117,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 6380
    identity := "34cdfbc30ee47c5dc51cab4a8d0794acfcaf03096a937a31b2be28d965000559" }
  checked := by decide +kernel

theorem w0434_check : PointSegmentLeaf.check w0434.data.points
    (Quadratic3.ofRat w0434.data.radiusSquared) w0434.data.witness = true := w0434.checked

def w0435 : CheckedWitness where
  data := {
    family := .q45
    factId := 6534
    role := 5
    anchorId := 371
    pointIds := [371,187,198,199,200,202,203,208,209,210,211,212,213,261,269,279,287,299,300,308,337,345,346,355]
    points := [p0208,p0187,p0198,p0199,p0200,p0202,p0203,p0208,p0209,p0210,p0211,p0212,p0213,p0261,p0269,p0279,p0287,p0299,p0300,p0308,p0334,p0342,p0343,p0352]
    radiusSquared := 1/4
    witness := .segment 18 20
    originalFlag := false
    sourceNI := true
    journalLine := 6535
    identity := "29ec2683f36d5bae0488bd99b4b68d90fc56bb26b7b0612ed24c18a242d3bf44" }
  checked := by decide +kernel

theorem w0435_check : PointSegmentLeaf.check w0435.data.points
    (Quadratic3.ofRat w0435.data.radiusSquared) w0435.data.witness = true := w0435.checked

def w0436 : CheckedWitness where
  data := {
    family := .q45
    factId := 6568
    role := 4
    anchorId := 370
    pointIds := [370,46,69,84,100,117,133,297]
    points := [p0100,p0046,p0069,p0084,p0100,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 6569
    identity := "c60cd63448ed0b1fb19b9abfd733614c216bebf7f9b172401b1fede7cb42c3b7" }
  checked := by decide +kernel

theorem w0436_check : PointSegmentLeaf.check w0436.data.points
    (Quadratic3.ofRat w0436.data.radiusSquared) w0436.data.witness = true := w0436.checked

def w0437 : CheckedWitness where
  data := {
    family := .q45
    factId := 6695
    role := 5
    anchorId := 371
    pointIds := [371,170,187,198,199,208,209,210,212,261,269,279,299,308,345]
    points := [p0208,p0170,p0187,p0198,p0199,p0208,p0209,p0210,p0212,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 6696
    identity := "65b442c41f9989408f8e9aa0ead6ddbebf1b9f96e538c14474fc24085ae34942" }
  checked := by decide +kernel

theorem w0437_check : PointSegmentLeaf.check w0437.data.points
    (Quadratic3.ofRat w0437.data.radiusSquared) w0437.data.witness = true := w0437.checked

def w0438 : CheckedWitness where
  data := {
    family := .q45
    factId := 7130
    role := 5
    anchorId := 371
    pointIds := [371,170,187,198,208,209,212,261,269,279,299,308,345]
    points := [p0208,p0170,p0187,p0198,p0208,p0209,p0212,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 7131
    identity := "cead46be263cf8863461f9724bd3743019e3e7aa32801503985a815c0fc86604" }
  checked := by decide +kernel

theorem w0438_check : PointSegmentLeaf.check w0438.data.points
    (Quadratic3.ofRat w0438.data.radiusSquared) w0438.data.witness = true := w0438.checked

def w0439 : CheckedWitness where
  data := {
    family := .q45
    factId := 7197
    role := 5
    anchorId := 371
    pointIds := [371,170,175,198,208,209,212,261,269,279,299,308,345]
    points := [p0208,p0170,p0175,p0198,p0208,p0209,p0212,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 7198
    identity := "ee91771062343731a832a3a964a1302d6eddf8aa809105098ab8d36bbed9e15f" }
  checked := by decide +kernel

theorem w0439_check : PointSegmentLeaf.check w0439.data.points
    (Quadratic3.ofRat w0439.data.radiusSquared) w0439.data.witness = true := w0439.checked

def w0440 : CheckedWitness where
  data := {
    family := .q45
    factId := 7323
    role := 5
    anchorId := 371
    pointIds := [371,104,208,209,261,269,279,299,308]
    points := [p0208,p0104,p0208,p0209,p0261,p0269,p0279,p0299,p0308]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 7324
    identity := "82e4d0df1429566345293f1e3f36e8ccee1b3c4363b09a607513444cb0dccca1" }
  checked := by decide +kernel

theorem w0440_check : PointSegmentLeaf.check w0440.data.points
    (Quadratic3.ofRat w0440.data.radiusSquared) w0440.data.witness = true := w0440.checked

def w0441 : CheckedWitness where
  data := {
    family := .q45
    factId := 7462
    role := 4
    anchorId := 370
    pointIds := [370,84,85,100,101,117,118,119,133,134,148,166,278,297,307]
    points := [p0100,p0084,p0085,p0100,p0101,p0117,p0118,p0119,p0133,p0134,p0148,p0166,p0278,p0297,p0307]
    radiusSquared := 1/4
    witness := .segment 1 11
    originalFlag := false
    sourceNI := true
    journalLine := 7463
    identity := "930be7692abf258356a00df0bb2bf8b0bda40ccb098b7b81cffb924fa2360393" }
  checked := by decide +kernel

theorem w0441_check : PointSegmentLeaf.check w0441.data.points
    (Quadratic3.ofRat w0441.data.radiusSquared) w0441.data.witness = true := w0441.checked

def w0442 : CheckedWitness where
  data := {
    family := .q45
    factId := 7496
    role := 5
    anchorId := 371
    pointIds := [371,136,180,189,191,198,199,200,201,202,208,209,210,211,212,261,269,279,287,299,308,345]
    points := [p0208,p0136,p0180,p0189,p0191,p0198,p0199,p0200,p0201,p0202,p0208,p0209,p0210,p0211,p0212,p0261,p0269,p0279,p0287,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 7497
    identity := "a3e4f9880ddb526b3369e95773d8a04c7dd3c49afa981c241062e7bd9f02660a" }
  checked := by decide +kernel

theorem w0442_check : PointSegmentLeaf.check w0442.data.points
    (Quadratic3.ofRat w0442.data.radiusSquared) w0442.data.witness = true := w0442.checked

def w0443 : CheckedWitness where
  data := {
    family := .q45
    factId := 7507
    role := 4
    anchorId := 370
    pointIds := [370,84,85,86,100,101,102,103,104,117,118,119,120,133,134,135,136,148,149,150,151,162,163,164,165,278,297,307]
    points := [p0100,p0084,p0085,p0086,p0100,p0101,p0102,p0103,p0104,p0117,p0118,p0119,p0120,p0133,p0134,p0135,p0136,p0148,p0149,p0150,p0151,p0162,p0163,p0164,p0165,p0278,p0297,p0307]
    radiusSquared := 1/4
    witness := .segment 8 20
    originalFlag := false
    sourceNI := true
    journalLine := 7508
    identity := "7a00a4a0162f0bfe1b3ebb84249de78298cb6158b38e1df5b5d028e4fa57e5da" }
  checked := by decide +kernel

theorem w0443_check : PointSegmentLeaf.check w0443.data.points
    (Quadratic3.ofRat w0443.data.radiusSquared) w0443.data.witness = true := w0443.checked

def w0444 : CheckedWitness where
  data := {
    family := .q45
    factId := 7509
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,101,117,118,119,133,134,148,166,278,297,307]
    points := [p0100,p0069,p0084,p0100,p0101,p0117,p0118,p0119,p0133,p0134,p0148,p0166,p0278,p0297,p0307]
    radiusSquared := 1/4
    witness := .segment 1 11
    originalFlag := false
    sourceNI := true
    journalLine := 7510
    identity := "2e5a69c42b5b8f50098653a1f59d076425a65ec15d410c16520f995b0588890f" }
  checked := by decide +kernel

theorem w0444_check : PointSegmentLeaf.check w0444.data.points
    (Quadratic3.ofRat w0444.data.radiusSquared) w0444.data.witness = true := w0444.checked

def w0445 : CheckedWitness where
  data := {
    family := .q45
    factId := 7566
    role := 5
    anchorId := 371
    pointIds := [371,136,180,187,188,189,192,198,199,200,201,202,203,208,209,210,211,212,213,261,269,279,287,299,308,345]
    points := [p0208,p0136,p0180,p0187,p0188,p0189,p0192,p0198,p0199,p0200,p0201,p0202,p0203,p0208,p0209,p0210,p0211,p0212,p0213,p0261,p0269,p0279,p0287,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 7567
    identity := "7a9e07889ecd9a18cef940874ba731052a7849db0b3c9b0105aa048914d0b5a3" }
  checked := by decide +kernel

theorem w0445_check : PointSegmentLeaf.check w0445.data.points
    (Quadratic3.ofRat w0445.data.radiusSquared) w0445.data.witness = true := w0445.checked

def w0446 : CheckedWitness where
  data := {
    family := .q45
    factId := 7884
    role := 5
    anchorId := 371
    pointIds := [371,162,170,208,209,261,269,279,299,308,345]
    points := [p0208,p0162,p0170,p0208,p0209,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 7885
    identity := "2c5e10b571554fa4cd64630734bfad3bfd32a80afe63a9f782394b5e07d6e780" }
  checked := by decide +kernel

theorem w0446_check : PointSegmentLeaf.check w0446.data.points
    (Quadratic3.ofRat w0446.data.radiusSquared) w0446.data.witness = true := w0446.checked

def w0447 : CheckedWitness where
  data := {
    family := .q45
    factId := 8112
    role := 5
    anchorId := 371
    pointIds := [371,104,208,209,212,261,269,279,345]
    points := [p0208,p0104,p0208,p0209,p0212,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 8113
    identity := "910bd73356931792bc682716c109fbb3a923586523ae7d34eb830cdb2efb208f" }
  checked := by decide +kernel

theorem w0447_check : PointSegmentLeaf.check w0447.data.points
    (Quadratic3.ofRat w0447.data.radiusSquared) w0447.data.witness = true := w0447.checked

def w0448 : CheckedWitness where
  data := {
    family := .q45
    factId := 8144
    role := 4
    anchorId := 370
    pointIds := [370,46,84,100,117,133,297]
    points := [p0100,p0046,p0084,p0100,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 8145
    identity := "cfb19882659cabe02b06547b728b8d3ecdf7732f8370aa36657f385498d34f0e" }
  checked := by decide +kernel

theorem w0448_check : PointSegmentLeaf.check w0448.data.points
    (Quadratic3.ofRat w0448.data.radiusSquared) w0448.data.witness = true := w0448.checked

def w0449 : CheckedWitness where
  data := {
    family := .q45
    factId := 8153
    role := 4
    anchorId := 370
    pointIds := [370,84,85,100,117,133,148,166,297]
    points := [p0100,p0084,p0085,p0100,p0117,p0133,p0148,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 8154
    identity := "65a0fe3ac8991bf0cfad01781b476a81c777cf7533758bc8f1f77e4d932e8ab3" }
  checked := by decide +kernel

theorem w0449_check : PointSegmentLeaf.check w0449.data.points
    (Quadratic3.ofRat w0449.data.radiusSquared) w0449.data.witness = true := w0449.checked

def w0450 : CheckedWitness where
  data := {
    family := .q45
    factId := 8242
    role := 5
    anchorId := 371
    pointIds := [371,104,208,209,261,269,279,299,308,345]
    points := [p0208,p0104,p0208,p0209,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 8243
    identity := "81098e4045c0fcdf6ca479bd4bb053be13f550279764fc811751c0d9688222fd" }
  checked := by decide +kernel

theorem w0450_check : PointSegmentLeaf.check w0450.data.points
    (Quadratic3.ofRat w0450.data.radiusSquared) w0450.data.witness = true := w0450.checked

def w0451 : CheckedWitness where
  data := {
    family := .q45
    factId := 8274
    role := 4
    anchorId := 370
    pointIds := [370,46,84,100,101,117,133,297]
    points := [p0100,p0046,p0084,p0100,p0101,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 8275
    identity := "677835eb450f146f0c499af4a63a22ae338f0a5785001b17422eec1472c1298e" }
  checked := by decide +kernel

theorem w0451_check : PointSegmentLeaf.check w0451.data.points
    (Quadratic3.ofRat w0451.data.radiusSquared) w0451.data.witness = true := w0451.checked

def w0452 : CheckedWitness where
  data := {
    family := .q45
    factId := 8450
    role := 5
    anchorId := 371
    pointIds := [371,170,187,198,208,209,210,261,269,279,299,308,345]
    points := [p0208,p0170,p0187,p0198,p0208,p0209,p0210,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 8451
    identity := "eb78be10a024e491177388f54fd9110bc1878863e382ba09770842ea17dd1962" }
  checked := by decide +kernel

theorem w0452_check : PointSegmentLeaf.check w0452.data.points
    (Quadratic3.ofRat w0452.data.radiusSquared) w0452.data.witness = true := w0452.checked

def w0453 : CheckedWitness where
  data := {
    family := .q45
    factId := 8541
    role := 4
    anchorId := 370
    pointIds := [370,30,46,69,84,100,101,117,133,297]
    points := [p0100,p0030,p0046,p0069,p0084,p0100,p0101,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 8542
    identity := "34fff07221578bc93ebea4c8bb81792b8f1f519c626d747f68b2c2bc2bc4f125" }
  checked := by decide +kernel

theorem w0453_check : PointSegmentLeaf.check w0453.data.points
    (Quadratic3.ofRat w0453.data.radiusSquared) w0453.data.witness = true := w0453.checked

def w0454 : CheckedWitness where
  data := {
    family := .q45
    factId := 8728
    role := 4
    anchorId := 370
    pointIds := [370,30,46,84,100,101,117,118,297]
    points := [p0100,p0030,p0046,p0084,p0100,p0101,p0117,p0118,p0297]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 8729
    identity := "cf68a4c7e849ecfb85083ac191ad11a2a5f11f6fd5aae4b3c1648051ef1c4e09" }
  checked := by decide +kernel

theorem w0454_check : PointSegmentLeaf.check w0454.data.points
    (Quadratic3.ofRat w0454.data.radiusSquared) w0454.data.witness = true := w0454.checked

def w0455 : CheckedWitness where
  data := {
    family := .q45
    factId := 8788
    role := 4
    anchorId := 370
    pointIds := [370,42,84,100,101,117,166,297]
    points := [p0100,p0042,p0084,p0100,p0101,p0117,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 8789
    identity := "b714668446b9e13965c99fc9e8baa73ab40510b4c57064985f72df0ddba99007" }
  checked := by decide +kernel

theorem w0455_check : PointSegmentLeaf.check w0455.data.points
    (Quadratic3.ofRat w0455.data.radiusSquared) w0455.data.witness = true := w0455.checked

def w0456 : CheckedWitness where
  data := {
    family := .q45
    factId := 8820
    role := 4
    anchorId := 370
    pointIds := [370,42,46,84,100,101,117,118,297]
    points := [p0100,p0042,p0046,p0084,p0100,p0101,p0117,p0118,p0297]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 8821
    identity := "638a2b2c3b253f0ecdff116167cbeb76077709e316200d0d7afcb7f810f7e4ea" }
  checked := by decide +kernel

theorem w0456_check : PointSegmentLeaf.check w0456.data.points
    (Quadratic3.ofRat w0456.data.radiusSquared) w0456.data.witness = true := w0456.checked

def w0457 : CheckedWitness where
  data := {
    family := .q45
    factId := 8824
    role := 5
    anchorId := 371
    pointIds := [371,170,187,198,208,209,210,211,261,269,279,299,308,345]
    points := [p0208,p0170,p0187,p0198,p0208,p0209,p0210,p0211,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 8825
    identity := "410d82481a7aeb38b24d42f66f43f0e08ac692d25a73b308d0b33b74636a3e31" }
  checked := by decide +kernel

theorem w0457_check : PointSegmentLeaf.check w0457.data.points
    (Quadratic3.ofRat w0457.data.radiusSquared) w0457.data.witness = true := w0457.checked

def w0458 : CheckedWitness where
  data := {
    family := .q45
    factId := 9110
    role := 4
    anchorId := 370
    pointIds := [370,84,100,117,187,288,297]
    points := [p0100,p0084,p0100,p0117,p0187,p0288,p0297]
    radiusSquared := 1/4
    witness := .segment 4 5
    originalFlag := false
    sourceNI := true
    journalLine := 9111
    identity := "0ca4c9b743db13ef02faf9a3b6b0a09a1b31247326709d268d2371e24cb89c28" }
  checked := by decide +kernel

theorem w0458_check : PointSegmentLeaf.check w0458.data.points
    (Quadratic3.ofRat w0458.data.radiusSquared) w0458.data.witness = true := w0458.checked

def w0459 : CheckedWitness where
  data := {
    family := .q45
    factId := 9628
    role := 4
    anchorId := 370
    pointIds := [370,46,69,84,100,101,117,133,297]
    points := [p0100,p0046,p0069,p0084,p0100,p0101,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 9629
    identity := "276a4c2526248b80918de275f88e61579cdc35a3061ce94c6dab7442358abf39" }
  checked := by decide +kernel

theorem w0459_check : PointSegmentLeaf.check w0459.data.points
    (Quadratic3.ofRat w0459.data.radiusSquared) w0459.data.witness = true := w0459.checked

def w0460 : CheckedWitness where
  data := {
    family := .q45
    factId := 10023
    role := 4
    anchorId := 370
    pointIds := [370,55,69,84,100,101,117,133,148,297,328,353,363]
    points := [p0100,p0055,p0069,p0084,p0100,p0101,p0117,p0133,p0148,p0297,p0325,p0350,p0360]
    radiusSquared := 1/4
    witness := .segment 1 10
    originalFlag := false
    sourceNI := true
    journalLine := 10024
    identity := "b4ad21555d14e3403bf8cbe1523719c87511a4b65b8630221f32c5db73977e01" }
  checked := by decide +kernel

theorem w0460_check : PointSegmentLeaf.check w0460.data.points
    (Quadratic3.ofRat w0460.data.radiusSquared) w0460.data.witness = true := w0460.checked

def w0461 : CheckedWitness where
  data := {
    family := .q45
    factId := 10841
    role := 4
    anchorId := 370
    pointIds := [370,55,69,84,100,101,117,118,133,297,328,335,353,363]
    points := [p0100,p0055,p0069,p0084,p0100,p0101,p0117,p0118,p0133,p0297,p0325,p0332,p0350,p0360]
    radiusSquared := 1/4
    witness := .segment 1 10
    originalFlag := false
    sourceNI := true
    journalLine := 10842
    identity := "9f1b957215e69da4eaa2d7e6e146937a23f6b1f3b84d77a071739304b3437bd0" }
  checked := by decide +kernel

theorem w0461_check : PointSegmentLeaf.check w0461.data.points
    (Quadratic3.ofRat w0461.data.radiusSquared) w0461.data.witness = true := w0461.checked

def w0462 : CheckedWitness where
  data := {
    family := .q45
    factId := 10959
    role := 4
    anchorId := 370
    pointIds := [370,58,69,84,85,100,101,102,117,118,177,297]
    points := [p0100,p0058,p0069,p0084,p0085,p0100,p0101,p0102,p0117,p0118,p0177,p0297]
    radiusSquared := 1/4
    witness := .segment 1 10
    originalFlag := false
    sourceNI := true
    journalLine := 10960
    identity := "98173a8c54dd98bde079277836b202d6b54dba95fe77115c1605972549f9429e" }
  checked := by decide +kernel

theorem w0462_check : PointSegmentLeaf.check w0462.data.points
    (Quadratic3.ofRat w0462.data.radiusSquared) w0462.data.witness = true := w0462.checked

def w0463 : CheckedWitness where
  data := {
    family := .q45
    factId := 10960
    role := 4
    anchorId := 370
    pointIds := [370,69,72,84,85,100,101,102,117,118,177,297]
    points := [p0100,p0069,p0072,p0084,p0085,p0100,p0101,p0102,p0117,p0118,p0177,p0297]
    radiusSquared := 1/4
    witness := .segment 2 10
    originalFlag := false
    sourceNI := true
    journalLine := 10961
    identity := "6e163c3695c3fae049e3015ab824d218256979c043fcd3410cf7ad7d75472e3f" }
  checked := by decide +kernel

theorem w0463_check : PointSegmentLeaf.check w0463.data.points
    (Quadratic3.ofRat w0463.data.radiusSquared) w0463.data.witness = true := w0463.checked

def w0464 : CheckedWitness where
  data := {
    family := .q45
    factId := 11032
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,101,117,133,166,297]
    points := [p0100,p0069,p0084,p0100,p0101,p0117,p0133,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 11033
    identity := "7958cdbbceada0c910378c08eb7394b0d71e9496d9b3090d9a2fba86603fb0ac" }
  checked := by decide +kernel

theorem w0464_check : PointSegmentLeaf.check w0464.data.points
    (Quadratic3.ofRat w0464.data.radiusSquared) w0464.data.witness = true := w0464.checked

def w0465 : CheckedWitness where
  data := {
    family := .q45
    factId := 11052
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,101,117,118,133,134,148,166,297]
    points := [p0100,p0069,p0084,p0100,p0101,p0117,p0118,p0133,p0134,p0148,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 10
    originalFlag := false
    sourceNI := true
    journalLine := 11053
    identity := "1ba8c3aebdcbeae8a78f89a89ac14c69bafe75760aaba7613ff81060ef575348" }
  checked := by decide +kernel

theorem w0465_check : PointSegmentLeaf.check w0465.data.points
    (Quadratic3.ofRat w0465.data.radiusSquared) w0465.data.witness = true := w0465.checked

def w0466 : CheckedWitness where
  data := {
    family := .q45
    factId := 11303
    role := 4
    anchorId := 370
    pointIds := [370,42,55,69,84,100,101,117,118,133,134,148,297,328,335,363]
    points := [p0100,p0042,p0055,p0069,p0084,p0100,p0101,p0117,p0118,p0133,p0134,p0148,p0297,p0325,p0332,p0360]
    radiusSquared := 1/4
    witness := .segment 1 13
    originalFlag := false
    sourceNI := true
    journalLine := 11304
    identity := "2582bd94eb74eb4a35692606f15e03a1b39d05f4701ec2a0db2d9e0a01db8df1" }
  checked := by decide +kernel

theorem w0466_check : PointSegmentLeaf.check w0466.data.points
    (Quadratic3.ofRat w0466.data.radiusSquared) w0466.data.witness = true := w0466.checked

def w0467 : CheckedWitness where
  data := {
    family := .q45
    factId := 11346
    role := 4
    anchorId := 370
    pointIds := [370,55,69,84,100,101,117,118,133,134,148,297,328,335,343,363]
    points := [p0100,p0055,p0069,p0084,p0100,p0101,p0117,p0118,p0133,p0134,p0148,p0297,p0325,p0332,p0340,p0360]
    radiusSquared := 1/4
    witness := .segment 1 12
    originalFlag := false
    sourceNI := true
    journalLine := 11347
    identity := "ffddde5d4d11e2d8ff1be47d4517e62eacac205e95a465dd3f9903122f09e908" }
  checked := by decide +kernel

theorem w0467_check : PointSegmentLeaf.check w0467.data.points
    (Quadratic3.ofRat w0467.data.radiusSquared) w0467.data.witness = true := w0467.checked

def w0468 : CheckedWitness where
  data := {
    family := .q45
    factId := 11538
    role := 4
    anchorId := 370
    pointIds := [370,55,69,84,100,101,117,118,133,134,148,297,328,335,353,363]
    points := [p0100,p0055,p0069,p0084,p0100,p0101,p0117,p0118,p0133,p0134,p0148,p0297,p0325,p0332,p0350,p0360]
    radiusSquared := 1/4
    witness := .segment 1 12
    originalFlag := false
    sourceNI := true
    journalLine := 11539
    identity := "249bcca216a17933ef23294f007bac7b96c6560ab04f909f033c2d7400e97791" }
  checked := by decide +kernel

theorem w0468_check : PointSegmentLeaf.check w0468.data.points
    (Quadratic3.ofRat w0468.data.radiusSquared) w0468.data.witness = true := w0468.checked

def w0469 : CheckedWitness where
  data := {
    family := .q45
    factId := 11932
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,166,297]
    points := [p0100,p0069,p0084,p0100,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 11933
    identity := "1d8af413ddc2b058d6b0a7605d5d3237cc7b4b3b7d9154b5c3753dd85cb77598" }
  checked := by decide +kernel

theorem w0469_check : PointSegmentLeaf.check w0469.data.points
    (Quadratic3.ofRat w0469.data.radiusSquared) w0469.data.witness = true := w0469.checked

def w0470 : CheckedWitness where
  data := {
    family := .q45
    factId := 11961
    role := 4
    anchorId := 370
    pointIds := [370,30,84,100,297,328]
    points := [p0100,p0030,p0084,p0100,p0297,p0325]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 11962
    identity := "abee931f2e25b3737334d6c6882a166410982e43e6e6f7e00281dd725c3bf8e5" }
  checked := by decide +kernel

theorem w0470_check : PointSegmentLeaf.check w0470.data.points
    (Quadratic3.ofRat w0470.data.radiusSquared) w0470.data.witness = true := w0470.checked

def w0471 : CheckedWitness where
  data := {
    family := .q45
    factId := 11964
    role := 5
    anchorId := 371
    pointIds := [371,170,187,198,208,209,261,269,279,345]
    points := [p0208,p0170,p0187,p0198,p0208,p0209,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 11965
    identity := "bf1fa7cfeca58daf68418dd71eb0b8a21a011fbcd1511fab9b22d0d4c4aca48a" }
  checked := by decide +kernel

theorem w0471_check : PointSegmentLeaf.check w0471.data.points
    (Quadratic3.ofRat w0471.data.radiusSquared) w0471.data.witness = true := w0471.checked

def w0472 : CheckedWitness where
  data := {
    family := .q45
    factId := 11972
    role := 5
    anchorId := 371
    pointIds := [371,104,175,187,198,208,209,261,269,279,299,308,345]
    points := [p0208,p0104,p0175,p0187,p0198,p0208,p0209,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 11973
    identity := "814aa4e4c41bce99e18f87c068f1875c0891b407f3f8d76c60cd2337898a126f" }
  checked := by decide +kernel

theorem w0472_check : PointSegmentLeaf.check w0472.data.points
    (Quadratic3.ofRat w0472.data.radiusSquared) w0472.data.witness = true := w0472.checked

def w0473 : CheckedWitness where
  data := {
    family := .q45
    factId := 12095
    role := 4
    anchorId := 370
    pointIds := [370,30,46,55,69,70,84,85,100,101,117,118,297,363]
    points := [p0100,p0030,p0046,p0055,p0069,p0070,p0084,p0085,p0100,p0101,p0117,p0118,p0297,p0360]
    radiusSquared := 1/4
    witness := .segment 2 9
    originalFlag := false
    sourceNI := true
    journalLine := 12096
    identity := "c2e1b932fceb822672820c4f0f5ca2a1052d75e4e9171a7a92f89fcddcb72ab7" }
  checked := by decide +kernel

theorem w0473_check : PointSegmentLeaf.check w0473.data.points
    (Quadratic3.ofRat w0473.data.radiusSquared) w0473.data.witness = true := w0473.checked

def w0474 : CheckedWitness where
  data := {
    family := .q45
    factId := 12136
    role := 4
    anchorId := 370
    pointIds := [370,30,46,55,69,84,100,101,117,133,297,363]
    points := [p0100,p0030,p0046,p0055,p0069,p0084,p0100,p0101,p0117,p0133,p0297,p0360]
    radiusSquared := 1/4
    witness := .segment 2 7
    originalFlag := false
    sourceNI := true
    journalLine := 12137
    identity := "b1e0a6e636aef3533c8a7e3ea73bba1ac596cc2bccabba29c5d65df473335172" }
  checked := by decide +kernel

theorem w0474_check : PointSegmentLeaf.check w0474.data.points
    (Quadratic3.ofRat w0474.data.radiusSquared) w0474.data.witness = true := w0474.checked

def w0475 : CheckedWitness where
  data := {
    family := .q45
    factId := 12289
    role := 4
    anchorId := 370
    pointIds := [370,30,46,55,69,84,100,101,117,118,297,363]
    points := [p0100,p0030,p0046,p0055,p0069,p0084,p0100,p0101,p0117,p0118,p0297,p0360]
    radiusSquared := 1/4
    witness := .segment 2 7
    originalFlag := false
    sourceNI := true
    journalLine := 12290
    identity := "a20c5b66a8e052459b613b8facae696bdb0ff58829cc83f3839717de1c9d34cf" }
  checked := by decide +kernel

theorem w0475_check : PointSegmentLeaf.check w0475.data.points
    (Quadratic3.ofRat w0475.data.radiusSquared) w0475.data.witness = true := w0475.checked

def w0476 : CheckedWitness where
  data := {
    family := .q45
    factId := 12348
    role := 5
    anchorId := 371
    pointIds := [371,104,187,198,208,209,261,269,279,299,308,345]
    points := [p0208,p0104,p0187,p0198,p0208,p0209,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 12349
    identity := "c24e11b2a5ab3bc76ed61cb448abfe37d1958e4ac4acbf4ee963699ec5368624" }
  checked := by decide +kernel

theorem w0476_check : PointSegmentLeaf.check w0476.data.points
    (Quadratic3.ofRat w0476.data.radiusSquared) w0476.data.witness = true := w0476.checked

def w0477 : CheckedWitness where
  data := {
    family := .q45
    factId := 13306
    role := 4
    anchorId := 370
    pointIds := [370,30,46,84,100,101,117,133,297]
    points := [p0100,p0030,p0046,p0084,p0100,p0101,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 13307
    identity := "2c9de9d9bfdb00328e1e26740e855f3439907a650bdb890e133b4b5a1f3d2b68" }
  checked := by decide +kernel

theorem w0477_check : PointSegmentLeaf.check w0477.data.points
    (Quadratic3.ofRat w0477.data.radiusSquared) w0477.data.witness = true := w0477.checked

def w0478 : CheckedWitness where
  data := {
    family := .q45
    factId := 14166
    role := 5
    anchorId := 371
    pointIds := [371,170,188,198,199,200,208,209,210,261,269,279,299,308,345]
    points := [p0208,p0170,p0188,p0198,p0199,p0200,p0208,p0209,p0210,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 14167
    identity := "20216bba0b6986e69ddfac4240c85c38ec243bcaf9fdbeac4630a63c5caaa895" }
  checked := by decide +kernel

theorem w0478_check : PointSegmentLeaf.check w0478.data.points
    (Quadratic3.ofRat w0478.data.radiusSquared) w0478.data.witness = true := w0478.checked

def w0479 : CheckedWitness where
  data := {
    family := .q45
    factId := 14209
    role := 4
    anchorId := 370
    pointIds := [370,30,69,84,100,101,117,133,297,328,363]
    points := [p0100,p0030,p0069,p0084,p0100,p0101,p0117,p0133,p0297,p0325,p0360]
    radiusSquared := 1/4
    witness := .segment 1 9
    originalFlag := false
    sourceNI := true
    journalLine := 14210
    identity := "95c28916b3de912c7281320325732ccdf2d4b3a9bafbe3e0a4ad36193758b4ac" }
  checked := by decide +kernel

theorem w0479_check : PointSegmentLeaf.check w0479.data.points
    (Quadratic3.ofRat w0479.data.radiusSquared) w0479.data.witness = true := w0479.checked

def w0480 : CheckedWitness where
  data := {
    family := .q45
    factId := 15575
    role := 4
    anchorId := 370
    pointIds := [370,30,42,55,56,69,71,84,100,101,102,117,118,119,133,134,148,297,300,325,343,353,363]
    points := [p0100,p0030,p0042,p0055,p0056,p0069,p0071,p0084,p0100,p0101,p0102,p0117,p0118,p0119,p0133,p0134,p0148,p0297,p0300,p0322,p0340,p0350,p0360]
    radiusSquared := 1/4
    witness := .segment 1 18
    originalFlag := false
    sourceNI := true
    journalLine := 15576
    identity := "3b170e3354cdb3045f28b81fb1270fac833f68abf1465d543b6a055f92cbf181" }
  checked := by decide +kernel

theorem w0480_check : PointSegmentLeaf.check w0480.data.points
    (Quadratic3.ofRat w0480.data.radiusSquared) w0480.data.witness = true := w0480.checked

def w0481 : CheckedWitness where
  data := {
    family := .q45
    factId := 15870
    role := 4
    anchorId := 370
    pointIds := [370,31,42,55,56,69,70,71,84,85,100,101,117,151,297]
    points := [p0100,p0031,p0042,p0055,p0056,p0069,p0070,p0071,p0084,p0085,p0100,p0101,p0117,p0151,p0297]
    radiusSquared := 1/4
    witness := .segment 1 13
    originalFlag := false
    sourceNI := true
    journalLine := 15871
    identity := "b75b9685dc477f9e030c1fe3c46a7a81f46621c2ce8c6175d59920bc3e778c13" }
  checked := by decide +kernel

theorem w0481_check : PointSegmentLeaf.check w0481.data.points
    (Quadratic3.ofRat w0481.data.radiusSquared) w0481.data.witness = true := w0481.checked

def w0482 : CheckedWitness where
  data := {
    family := .q45
    factId := 15871
    role := 4
    anchorId := 370
    pointIds := [370,42,44,55,56,69,70,71,84,85,100,101,117,151,297]
    points := [p0100,p0042,p0044,p0055,p0056,p0069,p0070,p0071,p0084,p0085,p0100,p0101,p0117,p0151,p0297]
    radiusSquared := 1/4
    witness := .segment 2 13
    originalFlag := false
    sourceNI := true
    journalLine := 15872
    identity := "438d7b509bea15800fab909d5a51fb29c21072f686ba8a6da8520b331a30504b" }
  checked := by decide +kernel

theorem w0482_check : PointSegmentLeaf.check w0482.data.points
    (Quadratic3.ofRat w0482.data.radiusSquared) w0482.data.witness = true := w0482.checked

def w0483 : CheckedWitness where
  data := {
    family := .q45
    factId := 15873
    role := 4
    anchorId := 370
    pointIds := [370,42,55,56,69,70,71,72,84,85,100,101,117,151,297]
    points := [p0100,p0042,p0055,p0056,p0069,p0070,p0071,p0072,p0084,p0085,p0100,p0101,p0117,p0151,p0297]
    radiusSquared := 1/4
    witness := .segment 7 13
    originalFlag := false
    sourceNI := true
    journalLine := 15874
    identity := "3dfede28edcdb688684a105870f7c6b334feae01a457483dda77fee6bd843c5a" }
  checked := by decide +kernel

theorem w0483_check : PointSegmentLeaf.check w0483.data.points
    (Quadratic3.ofRat w0483.data.radiusSquared) w0483.data.witness = true := w0483.checked

def w0484 : CheckedWitness where
  data := {
    family := .q45
    factId := 16121
    role := 4
    anchorId := 370
    pointIds := [370,84,100,277,297,300]
    points := [p0100,p0084,p0100,p0277,p0297,p0300]
    radiusSquared := 1/4
    witness := .segment 3 5
    originalFlag := false
    sourceNI := true
    journalLine := 16122
    identity := "e298ea2822a4b08c0ff45725c81e23076ba542e93606b2c4a0f5f6b50a3ababe" }
  checked := by decide +kernel

theorem w0484_check : PointSegmentLeaf.check w0484.data.points
    (Quadratic3.ofRat w0484.data.radiusSquared) w0484.data.witness = true := w0484.checked

def w0485 : CheckedWitness where
  data := {
    family := .q45
    factId := 18601
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,101,117,133,148,166,297]
    points := [p0100,p0069,p0084,p0100,p0101,p0117,p0133,p0148,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 8
    originalFlag := false
    sourceNI := true
    journalLine := 18602
    identity := "c2bd6898ef6aa96bf5cc6a5c7d7c097583ec52ada960f46b0390ac00bf43cc83" }
  checked := by decide +kernel

theorem w0485_check : PointSegmentLeaf.check w0485.data.points
    (Quadratic3.ofRat w0485.data.radiusSquared) w0485.data.witness = true := w0485.checked

def w0486 : CheckedWitness where
  data := {
    family := .q45
    factId := 18900
    role := 4
    anchorId := 370
    pointIds := [370,84,100,101,117,133,187,288,297]
    points := [p0100,p0084,p0100,p0101,p0117,p0133,p0187,p0288,p0297]
    radiusSquared := 1/4
    witness := .segment 6 7
    originalFlag := false
    sourceNI := true
    journalLine := 18901
    identity := "64c6ccb74741b7e3dd5a8702bd62269bafe4249a0bcc24ce65bfca540a44f9cf" }
  checked := by decide +kernel

theorem w0486_check : PointSegmentLeaf.check w0486.data.points
    (Quadratic3.ofRat w0486.data.radiusSquared) w0486.data.witness = true := w0486.checked

def w0487 : CheckedWitness where
  data := {
    family := .q45
    factId := 19295
    role := 4
    anchorId := 370
    pointIds := [370,84,85,100,101,117,133,166,297]
    points := [p0100,p0084,p0085,p0100,p0101,p0117,p0133,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 19296
    identity := "43126cecf8710201df05dc1f2cc5b5cfc7da18482f02de000a10616493c341a1" }
  checked := by decide +kernel

theorem w0487_check : PointSegmentLeaf.check w0487.data.points
    (Quadratic3.ofRat w0487.data.radiusSquared) w0487.data.witness = true := w0487.checked

def w0488 : CheckedWitness where
  data := {
    family := .q45
    factId := 19639
    role := 4
    anchorId := 370
    pointIds := [370,55,58,69,84,100,101,117,133,134,148,149,150,162,297,326,363]
    points := [p0100,p0055,p0058,p0069,p0084,p0100,p0101,p0117,p0133,p0134,p0148,p0149,p0150,p0162,p0297,p0323,p0360]
    radiusSquared := 1/4
    witness := .segment 2 12
    originalFlag := false
    sourceNI := true
    journalLine := 19640
    identity := "98bed94d3eab0777deed7d0408745a1dc4b72dbe7056d396e37c0a8b1f4afd96" }
  checked := by decide +kernel

theorem w0488_check : PointSegmentLeaf.check w0488.data.points
    (Quadratic3.ofRat w0488.data.radiusSquared) w0488.data.witness = true := w0488.checked

def w0489 : CheckedWitness where
  data := {
    family := .q45
    factId := 19672
    role := 4
    anchorId := 370
    pointIds := [370,69,84,100,101,117,133,148,162,166,297]
    points := [p0100,p0069,p0084,p0100,p0101,p0117,p0133,p0148,p0162,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 9
    originalFlag := false
    sourceNI := true
    journalLine := 19673
    identity := "7da7941789b485b008dab29994f0c5dcca24de9bf3905ac3290de1ea096328f8" }
  checked := by decide +kernel

theorem w0489_check : PointSegmentLeaf.check w0489.data.points
    (Quadratic3.ofRat w0489.data.radiusSquared) w0489.data.witness = true := w0489.checked

def w0490 : CheckedWitness where
  data := {
    family := .q45
    factId := 20144
    role := 5
    anchorId := 371
    pointIds := [371,104,187,188,198,199,200,208,209,261,269,279,345]
    points := [p0208,p0104,p0187,p0188,p0198,p0199,p0200,p0208,p0209,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 20145
    identity := "493dfbb4dcb641c80ba6f9493a73788a93f2ac73baa348281e5c5817083b1354" }
  checked := by decide +kernel

theorem w0490_check : PointSegmentLeaf.check w0490.data.points
    (Quadratic3.ofRat w0490.data.radiusSquared) w0490.data.witness = true := w0490.checked

def w0491 : CheckedWitness where
  data := {
    family := .q45
    factId := 20270
    role := 5
    anchorId := 371
    pointIds := [371,170,175,208,209,261,269,279,345]
    points := [p0208,p0170,p0175,p0208,p0209,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 20271
    identity := "237c42a179c9bdf231a55b5d6235c791f2eca127aaf95b517ce7c83c5e0114c1" }
  checked := by decide +kernel

theorem w0491_check : PointSegmentLeaf.check w0491.data.points
    (Quadratic3.ofRat w0491.data.radiusSquared) w0491.data.witness = true := w0491.checked

def w0492 : CheckedWitness where
  data := {
    family := .q45
    factId := 20378
    role := 4
    anchorId := 370
    pointIds := [370,19,84,100,297,300]
    points := [p0100,p0019,p0084,p0100,p0297,p0300]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 20379
    identity := "a3c2865157ee245777cf944996966789e9164eb8890e50c7289c2e3a846bfaed" }
  checked := by decide +kernel

theorem w0492_check : PointSegmentLeaf.check w0492.data.points
    (Quadratic3.ofRat w0492.data.radiusSquared) w0492.data.witness = true := w0492.checked

def w0493 : CheckedWitness where
  data := {
    family := .q45
    factId := 21958
    role := 5
    anchorId := 371
    pointIds := [371,162,170,198,208,209,261,269,279,345]
    points := [p0208,p0162,p0170,p0198,p0208,p0209,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 21959
    identity := "eacbec90840ea84e892fb72a10700ae84b521533ba664c81375204c84eb65050" }
  checked := by decide +kernel

theorem w0493_check : PointSegmentLeaf.check w0493.data.points
    (Quadratic3.ofRat w0493.data.radiusSquared) w0493.data.witness = true := w0493.checked

def w0494 : CheckedWitness where
  data := {
    family := .q45
    factId := 22326
    role := 5
    anchorId := 371
    pointIds := [371,104,200,208,209,261,269,279,345]
    points := [p0208,p0104,p0200,p0208,p0209,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 22327
    identity := "d2579ee29fbe772b3924de6ace4d0ac2ad7b95f9fb5043288ceb30ad4555d6d3" }
  checked := by decide +kernel

theorem w0494_check : PointSegmentLeaf.check w0494.data.points
    (Quadratic3.ofRat w0494.data.radiusSquared) w0494.data.witness = true := w0494.checked

def w0495 : CheckedWitness where
  data := {
    family := .q45
    factId := 22329
    role := 4
    anchorId := 370
    pointIds := [370,42,84,100,117,166,297]
    points := [p0100,p0042,p0084,p0100,p0117,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 22330
    identity := "069f991685f63d706d47f850d3b56648def388536baf505f0139b4c70157eec9" }
  checked := by decide +kernel

theorem w0495_check : PointSegmentLeaf.check w0495.data.points
    (Quadratic3.ofRat w0495.data.radiusSquared) w0495.data.witness = true := w0495.checked

def w0496 : CheckedWitness where
  data := {
    family := .q45
    factId := 22334
    role := 4
    anchorId := 370
    pointIds := [370,42,84,100,117,297,328]
    points := [p0100,p0042,p0084,p0100,p0117,p0297,p0325]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 22335
    identity := "08a9fe90b737747fad670032a8bf7f6d1c279ceb2cb00b8f5fca8fc0d27598a5" }
  checked := by decide +kernel

theorem w0496_check : PointSegmentLeaf.check w0496.data.points
    (Quadratic3.ofRat w0496.data.radiusSquared) w0496.data.witness = true := w0496.checked

def w0497 : CheckedWitness where
  data := {
    family := .q45
    factId := 22335
    role := 5
    anchorId := 371
    pointIds := [371,170,187,200,208,209,261,269,279,345]
    points := [p0208,p0170,p0187,p0200,p0208,p0209,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 22336
    identity := "796879abd5f572e5c933b75e3c0113ab52a2d08200873e306a72c4650bb371f8" }
  checked := by decide +kernel

theorem w0497_check : PointSegmentLeaf.check w0497.data.points
    (Quadratic3.ofRat w0497.data.radiusSquared) w0497.data.witness = true := w0497.checked

def w0498 : CheckedWitness where
  data := {
    family := .q45
    factId := 22352
    role := 4
    anchorId := 370
    pointIds := [370,42,46,69,84,100,101,117,133,297,325,343,353]
    points := [p0100,p0042,p0046,p0069,p0084,p0100,p0101,p0117,p0133,p0297,p0322,p0340,p0350]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 22353
    identity := "e77bceeaf8e95c3596a1b4414e48956bf2cb5e5bc3147c29828e11829245486a" }
  checked := by decide +kernel

theorem w0498_check : PointSegmentLeaf.check w0498.data.points
    (Quadratic3.ofRat w0498.data.radiusSquared) w0498.data.witness = true := w0498.checked

def w0499 : CheckedWitness where
  data := {
    family := .q45
    factId := 22562
    role := 4
    anchorId := 370
    pointIds := [370,30,42,43,55,57,69,84,100,101,104,117,133,270,297,325,343,353]
    points := [p0100,p0030,p0042,p0043,p0055,p0057,p0069,p0084,p0100,p0101,p0104,p0117,p0133,p0270,p0297,p0322,p0340,p0350]
    radiusSquared := 1/4
    witness := .segment 10 13
    originalFlag := false
    sourceNI := true
    journalLine := 22563
    identity := "f4851a22a095a9b3dd09603c96da32129e52474c8fa6cdc506ae31917b2ffe2e" }
  checked := by decide +kernel

theorem w0499_check : PointSegmentLeaf.check w0499.data.points
    (Quadratic3.ofRat w0499.data.radiusSquared) w0499.data.witness = true := w0499.checked

def w0500 : CheckedWitness where
  data := {
    family := .q45
    factId := 22564
    role := 4
    anchorId := 370
    pointIds := [370,30,42,43,55,57,69,84,100,101,117,133,136,270,297,325,343,353]
    points := [p0100,p0030,p0042,p0043,p0055,p0057,p0069,p0084,p0100,p0101,p0117,p0133,p0136,p0270,p0297,p0322,p0340,p0350]
    radiusSquared := 1/4
    witness := .segment 12 13
    originalFlag := false
    sourceNI := true
    journalLine := 22565
    identity := "47117cefa15b2a1a321402f36cefd05add8fc3d4ab041cfd5d74a091ae941465" }
  checked := by decide +kernel

theorem w0500_check : PointSegmentLeaf.check w0500.data.points
    (Quadratic3.ofRat w0500.data.radiusSquared) w0500.data.witness = true := w0500.checked

def w0501 : CheckedWitness where
  data := {
    family := .q45
    factId := 22566
    role := 5
    anchorId := 371
    pointIds := [371,135,136,162,163,164,166,175,176,177,187,189,198,200,208,209,261,269,279,299,308,345]
    points := [p0208,p0135,p0136,p0162,p0163,p0164,p0166,p0175,p0176,p0177,p0187,p0189,p0198,p0200,p0208,p0209,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 22567
    identity := "7dcc58247659dbc30d5179622e422a1439de7a4a73d4f98cbba7937caab612e5" }
  checked := by decide +kernel

theorem w0501_check : PointSegmentLeaf.check w0501.data.points
    (Quadratic3.ofRat w0501.data.radiusSquared) w0501.data.witness = true := w0501.checked

def w0502 : CheckedWitness where
  data := {
    family := .q45
    factId := 22567
    role := 5
    anchorId := 371
    pointIds := [371,135,136,162,163,164,175,176,177,180,187,189,198,200,208,209,261,269,279,299,308,345]
    points := [p0208,p0135,p0136,p0162,p0163,p0164,p0175,p0176,p0177,p0180,p0187,p0189,p0198,p0200,p0208,p0209,p0261,p0269,p0279,p0299,p0308,p0342]
    radiusSquared := 1/4
    witness := .segment 2 9
    originalFlag := false
    sourceNI := true
    journalLine := 22568
    identity := "9a10ee78554decbd2fbabfb8d2d783fc598e59b27f540462358f5b2d6b4e0931" }
  checked := by decide +kernel

theorem w0502_check : PointSegmentLeaf.check w0502.data.points
    (Quadratic3.ofRat w0502.data.radiusSquared) w0502.data.witness = true := w0502.checked

def w0503 : CheckedWitness where
  data := {
    family := .q45
    factId := 22671
    role := 4
    anchorId := 370
    pointIds := [370,30,42,43,55,56,57,69,84,85,100,101,117,136,270,297,325,343,353]
    points := [p0100,p0030,p0042,p0043,p0055,p0056,p0057,p0069,p0084,p0085,p0100,p0101,p0117,p0136,p0270,p0297,p0322,p0340,p0350]
    radiusSquared := 1/4
    witness := .segment 13 14
    originalFlag := false
    sourceNI := true
    journalLine := 22672
    identity := "3637d883ee06014b3bceaf6ff3dd3e7c460adb823a7edc6a4b452f7cb3db1bf8" }
  checked := by decide +kernel

theorem w0503_check : PointSegmentLeaf.check w0503.data.points
    (Quadratic3.ofRat w0503.data.radiusSquared) w0503.data.witness = true := w0503.checked

def w0504 : CheckedWitness where
  data := {
    family := .q45
    factId := 22747
    role := 4
    anchorId := 370
    pointIds := [370,30,42,43,55,56,57,69,70,84,85,86,100,101,117,136,270,286,297,325,343,353]
    points := [p0100,p0030,p0042,p0043,p0055,p0056,p0057,p0069,p0070,p0084,p0085,p0086,p0100,p0101,p0117,p0136,p0270,p0286,p0297,p0322,p0340,p0350]
    radiusSquared := 1/4
    witness := .segment 15 16
    originalFlag := false
    sourceNI := true
    journalLine := 22748
    identity := "ee2edde89868b7e1d6860367ef1c82540fe96cee466eff2aea95bd73062d2579" }
  checked := by decide +kernel

theorem w0504_check : PointSegmentLeaf.check w0504.data.points
    (Quadratic3.ofRat w0504.data.radiusSquared) w0504.data.witness = true := w0504.checked

def w0505 : CheckedWitness where
  data := {
    family := .q45
    factId := 23412
    role := 5
    anchorId := 371
    pointIds := [371,104,162,175,187,198,208,209,210,261,269,279,345]
    points := [p0208,p0104,p0162,p0175,p0187,p0198,p0208,p0209,p0210,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 23413
    identity := "c61c638f0e36fbf1db01122e9dee1d87df23266eeb6149a6462a1b7b915c1998" }
  checked := by decide +kernel

theorem w0505_check : PointSegmentLeaf.check w0505.data.points
    (Quadratic3.ofRat w0505.data.radiusSquared) w0505.data.witness = true := w0505.checked

def w0506 : CheckedWitness where
  data := {
    family := .q45
    factId := 25093
    role := 4
    anchorId := 370
    pointIds := [370,46,84,85,86,100,259,297]
    points := [p0100,p0046,p0084,p0085,p0086,p0100,p0259,p0297]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 25094
    identity := "1d728ba18b864524465b1231493aca3392e1653ca3bf8c3213dec76089fa2a21" }
  checked := by decide +kernel

theorem w0506_check : PointSegmentLeaf.check w0506.data.points
    (Quadratic3.ofRat w0506.data.radiusSquared) w0506.data.witness = true := w0506.checked

def w0507 : CheckedWitness where
  data := {
    family := .q45
    factId := 26847
    role := 4
    anchorId := 370
    pointIds := [370,30,100,297,328]
    points := [p0100,p0030,p0100,p0297,p0325]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 26848
    identity := "22e91c77f1300f36b9c53efa42506caea5e256a66d225027923e8a2be291ce2f" }
  checked := by decide +kernel

theorem w0507_check : PointSegmentLeaf.check w0507.data.points
    (Quadratic3.ofRat w0507.data.radiusSquared) w0507.data.witness = true := w0507.checked

def w0508 : CheckedWitness where
  data := {
    family := .q45
    factId := 26927
    role := 4
    anchorId := 370
    pointIds := [370,30,42,43,55,69,84,100,101,117,136,270,278,286,297]
    points := [p0100,p0030,p0042,p0043,p0055,p0069,p0084,p0100,p0101,p0117,p0136,p0270,p0278,p0286,p0297]
    radiusSquared := 1/4
    witness := .segment 10 11
    originalFlag := false
    sourceNI := true
    journalLine := 26928
    identity := "f93a68a4ecd42e65419021a3ba0ec760027d62ef84fbee626bc570b9d0b97564" }
  checked := by decide +kernel

theorem w0508_check : PointSegmentLeaf.check w0508.data.points
    (Quadratic3.ofRat w0508.data.radiusSquared) w0508.data.witness = true := w0508.checked

def w0509 : CheckedWitness where
  data := {
    family := .q45
    factId := 26934
    role := 5
    anchorId := 371
    pointIds := [371,119,162,163,164,175,176,180,187,198,199,200,208,209,261,269,279]
    points := [p0208,p0119,p0162,p0163,p0164,p0175,p0176,p0180,p0187,p0198,p0199,p0200,p0208,p0209,p0261,p0269,p0279]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 26935
    identity := "845bbafe64a80439016e2f4104d3986549c49b94adc2988591850d5ba56e8d4c" }
  checked := by decide +kernel

theorem w0509_check : PointSegmentLeaf.check w0509.data.points
    (Quadratic3.ofRat w0509.data.radiusSquared) w0509.data.witness = true := w0509.checked

def w0510 : CheckedWitness where
  data := {
    family := .q45
    factId := 26936
    role := 5
    anchorId := 371
    pointIds := [371,119,135,148,162,163,164,166,175,176,187,198,199,200,208,209,261,269,279]
    points := [p0208,p0119,p0135,p0148,p0162,p0163,p0164,p0166,p0175,p0176,p0187,p0198,p0199,p0200,p0208,p0209,p0261,p0269,p0279]
    radiusSquared := 1/4
    witness := .segment 1 7
    originalFlag := false
    sourceNI := true
    journalLine := 26937
    identity := "ed14c620bee91fec4eb878d5fa7cdef64c9287120bc58d1710dc1526f54cf29b" }
  checked := by decide +kernel

theorem w0510_check : PointSegmentLeaf.check w0510.data.points
    (Quadratic3.ofRat w0510.data.radiusSquared) w0510.data.witness = true := w0510.checked

def w0511 : CheckedWitness where
  data := {
    family := .q45
    factId := 27820
    role := 4
    anchorId := 370
    pointIds := [370,30,46,84,100,101,268,297]
    points := [p0100,p0030,p0046,p0084,p0100,p0101,p0268,p0297]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 27821
    identity := "48492de13e8cffc075fe357440d93dddf5e2f8b766f0f36e3c61a6a99e97b9d1" }
  checked := by decide +kernel

theorem w0511_check : PointSegmentLeaf.check w0511.data.points
    (Quadratic3.ofRat w0511.data.radiusSquared) w0511.data.witness = true := w0511.checked

def w0512 : CheckedWitness where
  data := {
    family := .q45
    factId := 28365
    role := 4
    anchorId := 370
    pointIds := [370,30,46,84,100,101,268,277,297]
    points := [p0100,p0030,p0046,p0084,p0100,p0101,p0268,p0277,p0297]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 28366
    identity := "4bed867013a4e1945eeed8836cc581a9662aa80ef397eec246cb38b89a4ab2b7" }
  checked := by decide +kernel

theorem w0512_check : PointSegmentLeaf.check w0512.data.points
    (Quadratic3.ofRat w0512.data.radiusSquared) w0512.data.witness = true := w0512.checked

def w0513 : CheckedWitness where
  data := {
    family := .q45
    factId := 28515
    role := 4
    anchorId := 370
    pointIds := [370,46,84,85,86,100,268,297]
    points := [p0100,p0046,p0084,p0085,p0086,p0100,p0268,p0297]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 28516
    identity := "cc4b88fcd71369c0cc5c18f82f508f34f6d45c4d22edfdde4b5c6bd068633efb" }
  checked := by decide +kernel

theorem w0513_check : PointSegmentLeaf.check w0513.data.points
    (Quadratic3.ofRat w0513.data.radiusSquared) w0513.data.witness = true := w0513.checked

def w0514 : CheckedWitness where
  data := {
    family := .q45
    factId := 28838
    role := 4
    anchorId := 370
    pointIds := [370,19,30,46,84,100,101,268,297]
    points := [p0100,p0019,p0030,p0046,p0084,p0100,p0101,p0268,p0297]
    radiusSquared := 1/4
    witness := .segment 3 6
    originalFlag := false
    sourceNI := true
    journalLine := 28839
    identity := "9a01517e637ce54a54abc8c49dd80a882ffcc80456dfbd363eaa7c1ccf0f38ff" }
  checked := by decide +kernel

theorem w0514_check : PointSegmentLeaf.check w0514.data.points
    (Quadratic3.ofRat w0514.data.radiusSquared) w0514.data.witness = true := w0514.checked

def w0515 : CheckedWitness where
  data := {
    family := .q45
    factId := 29250
    role := 4
    anchorId := 370
    pointIds := [370,19,30,46,84,100,101,268,277,297]
    points := [p0100,p0019,p0030,p0046,p0084,p0100,p0101,p0268,p0277,p0297]
    radiusSquared := 1/4
    witness := .segment 3 6
    originalFlag := false
    sourceNI := true
    journalLine := 29251
    identity := "93c89540d52d8d2c64b792ec2b703f936c646c5bbe83ff2997de25f85d745600" }
  checked := by decide +kernel

theorem w0515_check : PointSegmentLeaf.check w0515.data.points
    (Quadratic3.ofRat w0515.data.radiusSquared) w0515.data.witness = true := w0515.checked

def w0516 : CheckedWitness where
  data := {
    family := .q45
    factId := 29919
    role := 4
    anchorId := 370
    pointIds := [370,30,46,84,100,101,259,268,297]
    points := [p0100,p0030,p0046,p0084,p0100,p0101,p0259,p0268,p0297]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 29920
    identity := "0085bc5398371814f1befc0abdcc70697777acf07bacef4ce154c617981c37c8" }
  checked := by decide +kernel

theorem w0516_check : PointSegmentLeaf.check w0516.data.points
    (Quadratic3.ofRat w0516.data.radiusSquared) w0516.data.witness = true := w0516.checked

def w0517 : CheckedWitness where
  data := {
    family := .q45
    factId := 30332
    role := 4
    anchorId := 370
    pointIds := [370,30,46,84,100,101,259,268,277,297]
    points := [p0100,p0030,p0046,p0084,p0100,p0101,p0259,p0268,p0277,p0297]
    radiusSquared := 1/4
    witness := .segment 2 5
    originalFlag := false
    sourceNI := true
    journalLine := 30333
    identity := "5c2c5dff0977b1c7b05e56aa3737e2e04f4cd14a34522d40a241ed0cafc15830" }
  checked := by decide +kernel

theorem w0517_check : PointSegmentLeaf.check w0517.data.points
    (Quadratic3.ofRat w0517.data.radiusSquared) w0517.data.witness = true := w0517.checked

def w0518 : CheckedWitness where
  data := {
    family := .q45
    factId := 30482
    role := 4
    anchorId := 370
    pointIds := [370,46,84,85,86,100,259,268,297]
    points := [p0100,p0046,p0084,p0085,p0086,p0100,p0259,p0268,p0297]
    radiusSquared := 1/4
    witness := .segment 1 4
    originalFlag := false
    sourceNI := true
    journalLine := 30483
    identity := "ca3e5768d298f431f85ca04a50fff647e8bf992ae767f8105f7bfd7fb5d5c825" }
  checked := by decide +kernel

theorem w0518_check : PointSegmentLeaf.check w0518.data.points
    (Quadratic3.ofRat w0518.data.radiusSquared) w0518.data.witness = true := w0518.checked

def w0519 : CheckedWitness where
  data := {
    family := .q45
    factId := 30814
    role := 4
    anchorId := 370
    pointIds := [370,19,30,46,84,100,101,259,268,297]
    points := [p0100,p0019,p0030,p0046,p0084,p0100,p0101,p0259,p0268,p0297]
    radiusSquared := 1/4
    witness := .segment 3 6
    originalFlag := false
    sourceNI := true
    journalLine := 30815
    identity := "33ed18e3cae678b90a5409da991291449e2dcbf07dc029b386476d08084cd2c8" }
  checked := by decide +kernel

theorem w0519_check : PointSegmentLeaf.check w0519.data.points
    (Quadratic3.ofRat w0519.data.radiusSquared) w0519.data.witness = true := w0519.checked

def w0520 : CheckedWitness where
  data := {
    family := .q45
    factId := 31619
    role := 4
    anchorId := 370
    pointIds := [370,19,30,46,84,100,101,259,268,277,297]
    points := [p0100,p0019,p0030,p0046,p0084,p0100,p0101,p0259,p0268,p0277,p0297]
    radiusSquared := 1/4
    witness := .segment 3 6
    originalFlag := false
    sourceNI := true
    journalLine := 31620
    identity := "46c1bc077a4f8d6b789911f5a9b9a4bd5a16df0fd446bc93e2f0f38d685a8566" }
  checked := by decide +kernel

theorem w0520_check : PointSegmentLeaf.check w0520.data.points
    (Quadratic3.ofRat w0520.data.radiusSquared) w0520.data.witness = true := w0520.checked

def w0521 : CheckedWitness where
  data := {
    family := .q45
    factId := 32529
    role := 4
    anchorId := 370
    pointIds := [370,30,42,46,84,100,101,268,297]
    points := [p0100,p0030,p0042,p0046,p0084,p0100,p0101,p0268,p0297]
    radiusSquared := 1/4
    witness := .segment 3 6
    originalFlag := false
    sourceNI := true
    journalLine := 32530
    identity := "c03cdd1bac00f8cc878e613029e71c6b90c46b6aae2ea4053493cb609f388901" }
  checked := by decide +kernel

theorem w0521_check : PointSegmentLeaf.check w0521.data.points
    (Quadratic3.ofRat w0521.data.radiusSquared) w0521.data.witness = true := w0521.checked

def w0522 : CheckedWitness where
  data := {
    family := .q45
    factId := 32941
    role := 5
    anchorId := 371
    pointIds := [371,119,148,149,162,166,187,198,199,208,261,269,279,326,345]
    points := [p0208,p0119,p0148,p0149,p0162,p0166,p0187,p0198,p0199,p0208,p0261,p0269,p0279,p0323,p0342]
    radiusSquared := 1/4
    witness := .segment 1 5
    originalFlag := false
    sourceNI := true
    journalLine := 32942
    identity := "4d4aa9f2ef8d0ded42559221c728d94341b40f441a8079ee09ddb3db8eab23d6" }
  checked := by decide +kernel

theorem w0522_check : PointSegmentLeaf.check w0522.data.points
    (Quadratic3.ofRat w0522.data.radiusSquared) w0522.data.witness = true := w0522.checked

def w0523 : CheckedWitness where
  data := {
    family := .q45
    factId := 33275
    role := 4
    anchorId := 370
    pointIds := [370,46,100,117,162,297]
    points := [p0100,p0046,p0100,p0117,p0162,p0297]
    radiusSquared := 1/4
    witness := .segment 1 3
    originalFlag := false
    sourceNI := true
    journalLine := 33276
    identity := "e8b4b7bb12360b8534fc7438ed22026af55704cf0d89d7be80ee53d050e26d67" }
  checked := by decide +kernel

theorem w0523_check : PointSegmentLeaf.check w0523.data.points
    (Quadratic3.ofRat w0523.data.radiusSquared) w0523.data.witness = true := w0523.checked

def w0524 : CheckedWitness where
  data := {
    family := .q45
    factId := 33449
    role := 4
    anchorId := 370
    pointIds := [370,84,100,117,133,187,288,297]
    points := [p0100,p0084,p0100,p0117,p0133,p0187,p0288,p0297]
    radiusSquared := 1/4
    witness := .segment 5 6
    originalFlag := false
    sourceNI := true
    journalLine := 33450
    identity := "644a9e902ef8a67b444cde4374c9b72c13ebf49d336008f57b9df3e9671eb572" }
  checked := by decide +kernel

theorem w0524_check : PointSegmentLeaf.check w0524.data.points
    (Quadratic3.ofRat w0524.data.radiusSquared) w0524.data.witness = true := w0524.checked

def w0525 : CheckedWitness where
  data := {
    family := .q45
    factId := 33888
    role := 4
    anchorId := 370
    pointIds := [370,55,84,100,117,133,166,297]
    points := [p0100,p0055,p0084,p0100,p0117,p0133,p0166,p0297]
    radiusSquared := 1/4
    witness := .segment 1 6
    originalFlag := false
    sourceNI := true
    journalLine := 33889
    identity := "256f5f2b1945acaaf5e5a27a51db5d1b503242da9cdba2de46910ea42e361744" }
  checked := by decide +kernel

theorem w0525_check : PointSegmentLeaf.check w0525.data.points
    (Quadratic3.ofRat w0525.data.radiusSquared) w0525.data.witness = true := w0525.checked

def w0526 : CheckedWitness where
  data := {
    family := .q45
    factId := 33975
    role := 4
    anchorId := 370
    pointIds := [370,30,46,100,117,133,297]
    points := [p0100,p0030,p0046,p0100,p0117,p0133,p0297]
    radiusSquared := 1/4
    witness := .segment 2 4
    originalFlag := false
    sourceNI := true
    journalLine := 33976
    identity := "a5c3d255ef5a9f141835c238038f5e428b802df872fd5b5aff6b81df51d354a1" }
  checked := by decide +kernel

theorem w0526_check : PointSegmentLeaf.check w0526.data.points
    (Quadratic3.ofRat w0526.data.radiusSquared) w0526.data.witness = true := w0526.checked

def w0527 : CheckedWitness where
  data := {
    family := .q45
    factId := 35860
    role := 5
    anchorId := 371
    pointIds := [371,170,187,198,208,261,345]
    points := [p0208,p0170,p0187,p0198,p0208,p0261,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 35861
    identity := "ecc5ff9bb8d70bd45957cd07770c7268352b9a6d9570a108cf88dd8d1748c0b3" }
  checked := by decide +kernel

theorem w0527_check : PointSegmentLeaf.check w0527.data.points
    (Quadratic3.ofRat w0527.data.radiusSquared) w0527.data.witness = true := w0527.checked

def w0528 : CheckedWitness where
  data := {
    family := .q45
    factId := 35902
    role := 4
    anchorId := 370
    pointIds := [370,19,30,31,42,46,55,69,84,85,86,100,259,297]
    points := [p0100,p0019,p0030,p0031,p0042,p0046,p0055,p0069,p0084,p0085,p0086,p0100,p0259,p0297]
    radiusSquared := 1/4
    witness := .segment 5 10
    originalFlag := false
    sourceNI := true
    journalLine := 35903
    identity := "0a3dfc705e5e565db448c827c713fae8bdd05b6c7f374d183b238770f9c0457a" }
  checked := by decide +kernel

theorem w0528_check : PointSegmentLeaf.check w0528.data.points
    (Quadratic3.ofRat w0528.data.radiusSquared) w0528.data.witness = true := w0528.checked

def w0529 : CheckedWitness where
  data := {
    family := .q45
    factId := 35969
    role := 5
    anchorId := 371
    pointIds := [371,170,187,198,208,261,279,345]
    points := [p0208,p0170,p0187,p0198,p0208,p0261,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 35970
    identity := "9a76ad8c617206cab9fe827577a2e839e2f91855f02f34181072657391f3d27d" }
  checked := by decide +kernel

theorem w0529_check : PointSegmentLeaf.check w0529.data.points
    (Quadratic3.ofRat w0529.data.radiusSquared) w0529.data.witness = true := w0529.checked

def w0530 : CheckedWitness where
  data := {
    family := .q45
    factId := 36125
    role := 4
    anchorId := 370
    pointIds := [370,30,46,69,84,100,101,117,118,286,297,306,343,353,363]
    points := [p0100,p0030,p0046,p0069,p0084,p0100,p0101,p0117,p0118,p0286,p0297,p0306,p0340,p0350,p0360]
    radiusSquared := 1/4
    witness := .segment 2 6
    originalFlag := false
    sourceNI := true
    journalLine := 36126
    identity := "cf072f4b43e1e1955461e026de71be7b25b14969657cc1b4a726967df381987f" }
  checked := by decide +kernel

theorem w0530_check : PointSegmentLeaf.check w0530.data.points
    (Quadratic3.ofRat w0530.data.radiusSquared) w0530.data.witness = true := w0530.checked

def w0531 : CheckedWitness where
  data := {
    family := .q45
    factId := 36168
    role := 5
    anchorId := 371
    pointIds := [371,170,187,208,261,269,279,345]
    points := [p0208,p0170,p0187,p0208,p0261,p0269,p0279,p0342]
    radiusSquared := 1/4
    witness := .segment 1 2
    originalFlag := false
    sourceNI := true
    journalLine := 36169
    identity := "35cdf0f6e96eebb8cf812d3485f40546176692d0df309b9070d2c7ba383527f7" }
  checked := by decide +kernel

theorem w0531_check : PointSegmentLeaf.check w0531.data.points
    (Quadratic3.ofRat w0531.data.radiusSquared) w0531.data.witness = true := w0531.checked

def w0532 : CheckedWitness where
  data := {
    family := .q45
    factId := 36422
    role := 4
    anchorId := 370
    pointIds := [370,30,46,84,101,118,297]
    points := [p0100,p0030,p0046,p0084,p0101,p0118,p0297]
    radiusSquared := 1/4
    witness := .segment 2 4
    originalFlag := false
    sourceNI := true
    journalLine := 36423
    identity := "ebe512a32703525bec27f96806ef5e63f9cfda18625020101892042828ea8ef0" }
  checked := by decide +kernel

theorem w0532_check : PointSegmentLeaf.check w0532.data.points
    (Quadratic3.ofRat w0532.data.radiusSquared) w0532.data.witness = true := w0532.checked

def rows : List CheckedWitness := [w0000,w0001,w0002,w0003,w0004,w0005,w0006,w0007,w0008,w0009,w0010,w0011,w0012,w0013,w0014,w0015,w0016,w0017,w0018,w0019,w0020,w0021,w0022,w0023,w0024,w0025,w0026,w0027,w0028,w0029,w0030,w0031,w0032,w0033,w0034,w0035,w0036,w0037,w0038,w0039,w0040,w0041,w0042,w0043,w0044,w0045,w0046,w0047,w0048,w0049,w0050,w0051,w0052,w0053,w0054,w0055,w0056,w0057,w0058,w0059,w0060,w0061,w0062,w0063,w0064,w0065,w0066,w0067,w0068,w0069,w0070,w0071,w0072,w0073,w0074,w0075,w0076,w0077,w0078,w0079,w0080,w0081,w0082,w0083,w0084,w0085,w0086,w0087,w0088,w0089,w0090,w0091,w0092,w0093,w0094,w0095,w0096,w0097,w0098,w0099,w0100,w0101,w0102,w0103,w0104,w0105,w0106,w0107,w0108,w0109,w0110,w0111,w0112,w0113,w0114,w0115,w0116,w0117,w0118,w0119,w0120,w0121,w0122,w0123,w0124,w0125,w0126,w0127,w0128,w0129,w0130,w0131,w0132,w0133,w0134,w0135,w0136,w0137,w0138,w0139,w0140,w0141,w0142,w0143,w0144,w0145,w0146,w0147,w0148,w0149,w0150,w0151,w0152,w0153,w0154,w0155,w0156,w0157,w0158,w0159,w0160,w0161,w0162,w0163,w0164,w0165,w0166,w0167,w0168,w0169,w0170,w0171,w0172,w0173,w0174,w0175,w0176,w0177,w0178,w0179,w0180,w0181,w0182,w0183,w0184,w0185,w0186,w0187,w0188,w0189,w0190,w0191,w0192,w0193,w0194,w0195,w0196,w0197,w0198,w0199,w0200,w0201,w0202,w0203,w0204,w0205,w0206,w0207,w0208,w0209,w0210,w0211,w0212,w0213,w0214,w0215,w0216,w0217,w0218,w0219,w0220,w0221,w0222,w0223,w0224,w0225,w0226,w0227,w0228,w0229,w0230,w0231,w0232,w0233,w0234,w0235,w0236,w0237,w0238,w0239,w0240,w0241,w0242,w0243,w0244,w0245,w0246,w0247,w0248,w0249,w0250,w0251,w0252,w0253,w0254,w0255,w0256,w0257,w0258,w0259,w0260,w0261,w0262,w0263,w0264,w0265,w0266,w0267,w0268,w0269,w0270,w0271,w0272,w0273,w0274,w0275,w0276,w0277,w0278,w0279,w0280,w0281,w0282,w0283,w0284,w0285,w0286,w0287,w0288,w0289,w0290,w0291,w0292,w0293,w0294,w0295,w0296,w0297,w0298,w0299,w0300,w0301,w0302,w0303,w0304,w0305,w0306,w0307,w0308,w0309,w0310,w0311,w0312,w0313,w0314,w0315,w0316,w0317,w0318,w0319,w0320,w0321,w0322,w0323,w0324,w0325,w0326,w0327,w0328,w0329,w0330,w0331,w0332,w0333,w0334,w0335,w0336,w0337,w0338,w0339,w0340,w0341,w0342,w0343,w0344,w0345,w0346,w0347,w0348,w0349,w0350,w0351,w0352,w0353,w0354,w0355,w0356,w0357,w0358,w0359,w0360,w0361,w0362,w0363,w0364,w0365,w0366,w0367,w0368,w0369,w0370,w0371,w0372,w0373,w0374,w0375,w0376,w0377,w0378,w0379,w0380,w0381,w0382,w0383,w0384,w0385,w0386,w0387,w0388,w0389,w0390,w0391,w0392,w0393,w0394,w0395,w0396,w0397,w0398,w0399,w0400,w0401,w0402,w0403,w0404,w0405,w0406,w0407,w0408,w0409,w0410,w0411,w0412,w0413,w0414,w0415,w0416,w0417,w0418,w0419,w0420,w0421,w0422,w0423,w0424,w0425,w0426,w0427,w0428,w0429,w0430,w0431,w0432,w0433,w0434,w0435,w0436,w0437,w0438,w0439,w0440,w0441,w0442,w0443,w0444,w0445,w0446,w0447,w0448,w0449,w0450,w0451,w0452,w0453,w0454,w0455,w0456,w0457,w0458,w0459,w0460,w0461,w0462,w0463,w0464,w0465,w0466,w0467,w0468,w0469,w0470,w0471,w0472,w0473,w0474,w0475,w0476,w0477,w0478,w0479,w0480,w0481,w0482,w0483,w0484,w0485,w0486,w0487,w0488,w0489,w0490,w0491,w0492,w0493,w0494,w0495,w0496,w0497,w0498,w0499,w0500,w0501,w0502,w0503,w0504,w0505,w0506,w0507,w0508,w0509,w0510,w0511,w0512,w0513,w0514,w0515,w0516,w0517,w0518,w0519,w0520,w0521,w0522,w0523,w0524,w0525,w0526,w0527,w0528,w0529,w0530,w0531,w0532]

theorem checked_count : rows.length = 533 := by decide +kernel

theorem all_excluded (w : CheckedWitness) (_hw : w ∈ rows) (T : UnitTriangle)
    (contained : ∀ p, p ∈ w.data.points → toPlane p ∈ T.region) :
    ¬ PointSegmentLeaf.NonIntruding T (Quadratic3.ofRat w.data.radiusSquared) :=
  w.excluded T contained

end HexagonCover.PointSegmentData
