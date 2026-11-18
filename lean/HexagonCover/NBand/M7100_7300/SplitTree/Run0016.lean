import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0015
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0016
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1295 : Block := .branch 79 ![21267650467859855013215526316597576065, 730750818665451459101842416358141509827966273026, 6148, 24584, 98320, 393248, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 888).pointIds 888), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq1295 : B1295.tree = HexagonCover.NBand.M7100_7300.SplitData.node1295 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1294 : Block := .branch 159 ![21267650467859855013215526316597576065, 1538, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 887).pointIds 887), B1295, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1294 : B1294.tree = HexagonCover.NBand.M7100_7300.SplitData.node1294 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1295
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1293 : Block := .branch 124 ![2535301201046754613352112062849, 1538, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![B1294, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq1293 : B1293.tree = HexagonCover.NBand.M7100_7300.SplitData.node1293 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1294
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1292 : Block := .branch 128 ![2535301201046754613352112062849, 1538, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B1293, (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq1292 : B1292.tree = HexagonCover.NBand.M7100_7300.SplitData.node1292 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1293
  · rfl
  · rfl
  · rfl

def B1291 : Block := .branch 138 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B1292, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1291 : B1291.tree = HexagonCover.NBand.M7100_7300.SplitData.node1291 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1292
  · rfl
  · rfl

def B1290 : Block := .branch 139 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B1291, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1290 : B1290.tree = HexagonCover.NBand.M7100_7300.SplitData.node1290 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1291
  · rfl
  · rfl

def B1289 : Block := .branch 140 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B1290, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1289 : B1289.tree = HexagonCover.NBand.M7100_7300.SplitData.node1289 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1290
  · rfl
  · rfl

def B1288 : Block := .branch 141 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B1289, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq1288 : B1288.tree = HexagonCover.NBand.M7100_7300.SplitData.node1288 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1289
  · rfl
  · rfl

def B1287 : Block := .branch 142 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B1288, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1287 : B1287.tree = HexagonCover.NBand.M7100_7300.SplitData.node1287 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1288
  · rfl
  · rfl

def B1286 : Block := .branch 165 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 840).pointIds 840), B1287, (.leaf 0 [] 0)]
theorem treeEq1286 : B1286.tree = HexagonCover.NBand.M7100_7300.SplitData.node1286 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1287
  · rfl

def B1285 : Block := .branch 167 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 839).pointIds 839), B1286, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1285 : B1285.tree = HexagonCover.NBand.M7100_7300.SplitData.node1285 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1286
  · rfl

def B1284 : Block := .branch 143 ![2535301201046754613352112062849, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 748288838313422294120286634350736906063837462396960, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), B1285, (.leaf 5 (Common.fact 837).pointIds 837), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq1284 : B1284.tree = HexagonCover.NBand.M7100_7300.SplitData.node1284 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1285
  · rfl
  · rfl

def B1283 : Block := .branch 170 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 8769009823985417509222147681923925786069185880072, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 836).pointIds 836), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1284]
theorem treeEq1283 : B1283.tree = HexagonCover.NBand.M7100_7300.SplitData.node1283 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1284

def B1282 : Block := .branch 161 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 907).pointIds 907), B1283, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq1282 : B1282.tree = HexagonCover.NBand.M7100_7300.SplitData.node1282 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1283
  · rfl
  · rfl
  · rfl

def B1281 : Block := .branch 75 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B1282, (.leaf 3 (Common.fact 707).pointIds 707), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq1281 : B1281.tree = HexagonCover.NBand.M7100_7300.SplitData.node1281 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1282
  · rfl
  · rfl
  · rfl
  · rfl

def B1280 : Block := .branch 162 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B1281, (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq1280 : B1280.tree = HexagonCover.NBand.M7100_7300.SplitData.node1280 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1281
  · rfl
  · rfl
  · rfl

def B1279 : Block := .branch 172 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 701).pointIds 701), (.leaf 5 (Common.fact 702).pointIds 702), B1280]
theorem treeEq1279 : B1279.tree = HexagonCover.NBand.M7100_7300.SplitData.node1279 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1280

def B1278 : Block := .branch 151 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B1279, (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq1278 : B1278.tree = HexagonCover.NBand.M7100_7300.SplitData.node1278 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1279
  · rfl
  · rfl

def B1277 : Block := .branch 132 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B1278]
theorem treeEq1277 : B1277.tree = HexagonCover.NBand.M7100_7300.SplitData.node1277 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1278

def B1276 : Block := .branch 78 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 140).pointIds 140), B1277, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq1276 : B1276.tree = HexagonCover.NBand.M7100_7300.SplitData.node1276 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1277
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1276 : B1276.accepted = true := by decide +kernel
theorem checked1276 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1276 (maskNeeds ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920]) := by
  rw [← treeEq1276]
  exact B1276.sound accepted1276
#print axioms checked1276

def Tip1268_1276 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1276 ![2535301201046754613352112062849, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] checked1276
def B1275 : Block := .branch 101 ![590295810358705652097, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![Tip1268_1276, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq1275 : B1275.tree = HexagonCover.NBand.M7100_7300.SplitData.node1275 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1274 : Block := .branch 133 ![590295810358705652097, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B1275]
theorem treeEq1274 : B1274.tree = HexagonCover.NBand.M7100_7300.SplitData.node1274 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1275

def B1273 : Block := .branch 157 ![590295810358705652097, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B1274, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq1273 : B1273.tree = HexagonCover.NBand.M7100_7300.SplitData.node1273 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1274
  · rfl
  · rfl

def B1272 : Block := .branch 169 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 909).pointIds 909), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), B1273, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq1272 : B1272.tree = HexagonCover.NBand.M7100_7300.SplitData.node1272 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1273
  · rfl

def B1303 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 855).pointIds 855), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq1303 : B1303.tree = HexagonCover.NBand.M7100_7300.SplitData.node1303 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1302 : Block := .branch 159 ![10384593717069655257060992658440577, 737869762948382066178, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![B1303, (.leaf 1 (Common.fact 931).pointIds 931), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq1302 : B1302.tree = HexagonCover.NBand.M7100_7300.SplitData.node1302 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1303
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1301 : Block := .branch 75 ![10384593717069655257060992658440577, 737869762948382066178, 6148, 2923003274661805836407369665432566039311865110536, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B1302, (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq1301 : B1301.tree = HexagonCover.NBand.M7100_7300.SplitData.node1301 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1302
  · rfl
  · rfl
  · rfl
  · rfl

def B1300 : Block := .branch 170 ![10384593717069655257060992658440577, 738013878136457922050, 18446745173221185540, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 850).pointIds 850), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1301]
theorem treeEq1300 : B1300.tree = HexagonCover.NBand.M7100_7300.SplitData.node1300 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1301

def B1299 : Block := .branch 161 ![10384593717069655257060992658440577, 738013878136457922050, 18446745173221185540, 24584, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 907).pointIds 907), B1300, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1299 : B1299.tree = HexagonCover.NBand.M7100_7300.SplitData.node1299 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1300
  · rfl
  · rfl
  · rfl

def B1298 : Block := .branch 172 ![10384593717069655257060992658440577, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B1299]
theorem treeEq1298 : B1298.tree = HexagonCover.NBand.M7100_7300.SplitData.node1298 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1299

def B1297 : Block := .branch 171 ![10384593717069655257060992658440577, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1298, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1297 : B1297.tree = HexagonCover.NBand.M7100_7300.SplitData.node1297 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1298
  · rfl
  · rfl

def B1296 : Block := .branch 160 ![10384593717069655257060992658440577, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1297]
theorem treeEq1296 : B1296.tree = HexagonCover.NBand.M7100_7300.SplitData.node1296 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1297

def B1271 : Block := .branch 69 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B1272, B1296, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1271 : B1271.tree = HexagonCover.NBand.M7100_7300.SplitData.node1271 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1272
  · exact treeEq1296
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1305 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1305 : B1305.tree = HexagonCover.NBand.M7100_7300.SplitData.node1305 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1304 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), B1305, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1304 : B1304.tree = HexagonCover.NBand.M7100_7300.SplitData.node1304 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1305
  · rfl
  · rfl

def B1270 : Block := .branch 68 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), B1271, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), B1304]
theorem treeEq1270 : B1270.tree = HexagonCover.NBand.M7100_7300.SplitData.node1270 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1271
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1304

def B1269 : Block := .branch 91 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B1270, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1269 : B1269.tree = HexagonCover.NBand.M7100_7300.SplitData.node1269 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1270
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1268 : Block := .branch 113 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B1269, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq1268 : B1268.tree = HexagonCover.NBand.M7100_7300.SplitData.node1268 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1269
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1268 : B1268.accepted = true := by decide +kernel
theorem checked1268 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1268 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq1268]
  exact B1268.sound accepted1268
#print axioms checked1268

def Tip1238_1241 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1241 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0015.checked1241
def Tip1238_1268 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1268 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] checked1268
def B1263 : Block := .branch 160 ![385, 302821750714015999329794, 18446745173221185540, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 929).pointIds 929), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1263 : B1263.tree = HexagonCover.NBand.M7100_7300.SplitData.node1263 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1262 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 828).pointIds 828), B1263, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1262 : B1262.tree = HexagonCover.NBand.M7100_7300.SplitData.node1262 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1263
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1261 : Block := .branch 169 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257130263143762513720633720896] ![B1262, (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 909).pointIds 909), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 827).pointIds 827)]
theorem treeEq1261 : B1261.tree = HexagonCover.NBand.M7100_7300.SplitData.node1261 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1262
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1260 : Block := .branch 151 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 823).pointIds 823), B1261, (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1260 : B1260.tree = HexagonCover.NBand.M7100_7300.SplitData.node1260 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1261
  · rfl

def B1259 : Block := .branch 172 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B1260]
theorem treeEq1259 : B1259.tree = HexagonCover.NBand.M7100_7300.SplitData.node1259 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1260

def B1258 : Block := .branch 171 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1259, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq1258 : B1258.tree = HexagonCover.NBand.M7100_7300.SplitData.node1258 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1259
  · rfl
  · rfl

def B1240 : Block := .branch 80 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip1238_1241, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B1258]
theorem treeEq1240 : B1240.tree = HexagonCover.NBand.M7100_7300.SplitData.node1240 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1258

def B1267 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 675).pointIds 675), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq1267 : B1267.tree = HexagonCover.NBand.M7100_7300.SplitData.node1267 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1266 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 5986310706529156424445550204162344646313448448720960] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1267, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1266 : B1266.tree = HexagonCover.NBand.M7100_7300.SplitData.node1266 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1267
  · rfl
  · rfl

def B1265 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B1266]
theorem treeEq1265 : B1265.tree = HexagonCover.NBand.M7100_7300.SplitData.node1265 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1266

def B1264 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1265, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq1264 : B1264.tree = HexagonCover.NBand.M7100_7300.SplitData.node1264 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1265
  · rfl
  · rfl

def B1239 : Block := .branch 78 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), B1240, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B1264]
theorem treeEq1239 : B1239.tree = HexagonCover.NBand.M7100_7300.SplitData.node1239 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1240
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1264

def B1238 : Block := .branch 76 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), B1239, (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), Tip1238_1268]
theorem treeEq1238 : B1238.tree = HexagonCover.NBand.M7100_7300.SplitData.node1238 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1239
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1238 : B1238.accepted = true := by decide +kernel
theorem checked1238 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1238 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1238]
  exact B1238.sound accepted1238
#print axioms checked1238

def Tip1237_1238 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1238 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1238
def B1317 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq1317 : B1317.tree = HexagonCover.NBand.M7100_7300.SplitData.node1317 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1316 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B1317]
theorem treeEq1316 : B1316.tree = HexagonCover.NBand.M7100_7300.SplitData.node1316 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1317

def B1315 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1316, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq1315 : B1315.tree = HexagonCover.NBand.M7100_7300.SplitData.node1315 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1316
  · rfl
  · rfl

def B1314 : Block := .branch 160 ![385, 604610627875092339623426, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1315]
theorem treeEq1314 : B1314.tree = HexagonCover.NBand.M7100_7300.SplitData.node1314 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1315

def B1313 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B1314, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1313 : B1313.tree = HexagonCover.NBand.M7100_7300.SplitData.node1313 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1314
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1312 : Block := .branch 124 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B1313, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1312 : B1312.tree = HexagonCover.NBand.M7100_7300.SplitData.node1312 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1313
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1311 : Block := .branch 163 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B1312]
theorem treeEq1311 : B1311.tree = HexagonCover.NBand.M7100_7300.SplitData.node1311 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1312

def B1310 : Block := .branch 165 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B1311, (.leaf 0 [] 0)]
theorem treeEq1310 : B1310.tree = HexagonCover.NBand.M7100_7300.SplitData.node1310 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1311
  · rfl

def B1309 : Block := .branch 167 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B1310, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1309 : B1309.tree = HexagonCover.NBand.M7100_7300.SplitData.node1309 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1310
  · rfl

def B1308 : Block := .branch 142 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B1309, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1308 : B1308.tree = HexagonCover.NBand.M7100_7300.SplitData.node1308 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1309
  · rfl
  · rfl

def B1307 : Block := .branch 144 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B1308, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1307 : B1307.tree = HexagonCover.NBand.M7100_7300.SplitData.node1307 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1308
  · rfl

def B1306 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1307]
theorem treeEq1306 : B1306.tree = HexagonCover.NBand.M7100_7300.SplitData.node1306 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1307

def B1237 : Block := .branch 74 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip1237_1238, B1306, (.leaf 4 (Common.fact 395).pointIds 395), (.leaf 5 (Common.fact 396).pointIds 396), (.leaf 6 (Common.fact 397).pointIds 397)]
theorem treeEq1237 : B1237.tree = HexagonCover.NBand.M7100_7300.SplitData.node1237 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1306
  · rfl
  · rfl
  · rfl

theorem accepted1237 : B1237.accepted = true := by decide +kernel
theorem checked1237 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1237 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1237]
  exact B1237.sound accepted1237
#print axioms checked1237

def Tip1236_1237 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1237 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1237
def B1329 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq1329 : B1329.tree = HexagonCover.NBand.M7100_7300.SplitData.node1329 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1328 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B1329]
theorem treeEq1328 : B1328.tree = HexagonCover.NBand.M7100_7300.SplitData.node1328 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1329

def B1327 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1328, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq1327 : B1327.tree = HexagonCover.NBand.M7100_7300.SplitData.node1327 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1328
  · rfl
  · rfl

def B1326 : Block := .branch 160 ![385, 604610627875092339623426, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1327]
theorem treeEq1326 : B1326.tree = HexagonCover.NBand.M7100_7300.SplitData.node1326 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1327

def B1325 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B1326, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1325 : B1325.tree = HexagonCover.NBand.M7100_7300.SplitData.node1325 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1326
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1324 : Block := .branch 124 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B1325, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1324 : B1324.tree = HexagonCover.NBand.M7100_7300.SplitData.node1324 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1325
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1323 : Block := .branch 163 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B1324]
theorem treeEq1323 : B1323.tree = HexagonCover.NBand.M7100_7300.SplitData.node1323 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1324

def B1322 : Block := .branch 165 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B1323, (.leaf 0 [] 0)]
theorem treeEq1322 : B1322.tree = HexagonCover.NBand.M7100_7300.SplitData.node1322 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1323
  · rfl

def B1321 : Block := .branch 167 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B1322, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1321 : B1321.tree = HexagonCover.NBand.M7100_7300.SplitData.node1321 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1322
  · rfl

def B1320 : Block := .branch 142 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B1321, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1320 : B1320.tree = HexagonCover.NBand.M7100_7300.SplitData.node1320 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1321
  · rfl
  · rfl

def B1319 : Block := .branch 144 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B1320, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1319 : B1319.tree = HexagonCover.NBand.M7100_7300.SplitData.node1319 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1320
  · rfl

def B1318 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 772).pointIds 772), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1319]
theorem treeEq1318 : B1318.tree = HexagonCover.NBand.M7100_7300.SplitData.node1318 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1319

def B1236 : Block := .branch 73 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip1236_1237, B1318, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq1236 : B1236.tree = HexagonCover.NBand.M7100_7300.SplitData.node1236 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1318
  · rfl
  · rfl
  · rfl

theorem accepted1236 : B1236.accepted = true := by decide +kernel
theorem checked1236 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1236 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1236]
  exact B1236.sound accepted1236
#print axioms checked1236

end HexagonCover.NBand.M7100_7300.SplitTree.Run0016
