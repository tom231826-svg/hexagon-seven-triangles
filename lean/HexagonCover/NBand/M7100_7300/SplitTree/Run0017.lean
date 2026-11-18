import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0011
import HexagonCover.NBand.M7100_7300.SplitTree.Run0013
import HexagonCover.NBand.M7100_7300.SplitTree.Run0016
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0017
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1235_1236 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1236 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0016.checked1236
def B1341 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq1341 : B1341.tree = HexagonCover.NBand.M7100_7300.SplitData.node1341 := by
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

def B1340 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B1341]
theorem treeEq1340 : B1340.tree = HexagonCover.NBand.M7100_7300.SplitData.node1340 := by
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
  · exact treeEq1341

def B1339 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1340, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq1339 : B1339.tree = HexagonCover.NBand.M7100_7300.SplitData.node1339 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1340
  · rfl
  · rfl

def B1338 : Block := .branch 160 ![385, 604610627875092339623426, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1339]
theorem treeEq1338 : B1338.tree = HexagonCover.NBand.M7100_7300.SplitData.node1338 := by
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
  · exact treeEq1339

def B1337 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B1338, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1337 : B1337.tree = HexagonCover.NBand.M7100_7300.SplitData.node1337 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1338
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1336 : Block := .branch 124 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B1337, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1336 : B1336.tree = HexagonCover.NBand.M7100_7300.SplitData.node1336 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1337
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1335 : Block := .branch 163 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B1336]
theorem treeEq1335 : B1335.tree = HexagonCover.NBand.M7100_7300.SplitData.node1335 := by
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
  · exact treeEq1336

def B1334 : Block := .branch 165 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B1335, (.leaf 0 [] 0)]
theorem treeEq1334 : B1334.tree = HexagonCover.NBand.M7100_7300.SplitData.node1334 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1335
  · rfl

def B1333 : Block := .branch 167 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B1334, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1333 : B1333.tree = HexagonCover.NBand.M7100_7300.SplitData.node1333 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1334
  · rfl

def B1332 : Block := .branch 142 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B1333, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1332 : B1332.tree = HexagonCover.NBand.M7100_7300.SplitData.node1332 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1333
  · rfl
  · rfl

def B1331 : Block := .branch 144 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B1332, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1331 : B1331.tree = HexagonCover.NBand.M7100_7300.SplitData.node1331 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1332
  · rfl

def B1330 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1331]
theorem treeEq1330 : B1330.tree = HexagonCover.NBand.M7100_7300.SplitData.node1330 := by
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
  · exact treeEq1331

def B1235 : Block := .branch 72 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip1235_1236, B1330, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq1235 : B1235.tree = HexagonCover.NBand.M7100_7300.SplitData.node1235 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1330
  · rfl
  · rfl
  · rfl

theorem accepted1235 : B1235.accepted = true := by decide +kernel
theorem checked1235 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1235 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1235]
  exact B1235.sound accepted1235
#print axioms checked1235

def Tip1232_1235 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1235 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1235
def B1353 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq1353 : B1353.tree = HexagonCover.NBand.M7100_7300.SplitData.node1353 := by
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

def B1352 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B1353]
theorem treeEq1352 : B1352.tree = HexagonCover.NBand.M7100_7300.SplitData.node1352 := by
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
  · exact treeEq1353

def B1351 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1352, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq1351 : B1351.tree = HexagonCover.NBand.M7100_7300.SplitData.node1351 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1352
  · rfl
  · rfl

def B1350 : Block := .branch 160 ![385, 604610627875092339623426, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1351]
theorem treeEq1350 : B1350.tree = HexagonCover.NBand.M7100_7300.SplitData.node1350 := by
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
  · exact treeEq1351

def B1349 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B1350, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1349 : B1349.tree = HexagonCover.NBand.M7100_7300.SplitData.node1349 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1350
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1348 : Block := .branch 124 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B1349, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1348 : B1348.tree = HexagonCover.NBand.M7100_7300.SplitData.node1348 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1349
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1347 : Block := .branch 163 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B1348]
theorem treeEq1347 : B1347.tree = HexagonCover.NBand.M7100_7300.SplitData.node1347 := by
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
  · exact treeEq1348

def B1346 : Block := .branch 165 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B1347, (.leaf 0 [] 0)]
theorem treeEq1346 : B1346.tree = HexagonCover.NBand.M7100_7300.SplitData.node1346 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1347
  · rfl

def B1345 : Block := .branch 167 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B1346, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1345 : B1345.tree = HexagonCover.NBand.M7100_7300.SplitData.node1345 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1346
  · rfl

def B1344 : Block := .branch 142 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B1345, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1344 : B1344.tree = HexagonCover.NBand.M7100_7300.SplitData.node1344 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1345
  · rfl
  · rfl

def B1343 : Block := .branch 144 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B1344, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1343 : B1343.tree = HexagonCover.NBand.M7100_7300.SplitData.node1343 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1344
  · rfl

def B1342 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 784).pointIds 784), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1343]
theorem treeEq1342 : B1342.tree = HexagonCover.NBand.M7100_7300.SplitData.node1342 := by
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
  · exact treeEq1343

def B1234 : Block := .branch 71 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip1232_1235, B1342, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq1234 : B1234.tree = HexagonCover.NBand.M7100_7300.SplitData.node1234 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1342
  · rfl
  · rfl
  · rfl

def B1355 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq1355 : B1355.tree = HexagonCover.NBand.M7100_7300.SplitData.node1355 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1354 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), B1355, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq1354 : B1354.tree = HexagonCover.NBand.M7100_7300.SplitData.node1354 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1355
  · rfl
  · rfl

def B1233 : Block := .branch 67 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 378).pointIds 378), B1234, (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), B1354]
theorem treeEq1233 : B1233.tree = HexagonCover.NBand.M7100_7300.SplitData.node1233 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1234
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1354

def B1357 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq1357 : B1357.tree = HexagonCover.NBand.M7100_7300.SplitData.node1357 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1356 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), B1357, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq1356 : B1356.tree = HexagonCover.NBand.M7100_7300.SplitData.node1356 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1357
  · rfl
  · rfl

def B1232 : Block := .branch 65 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), B1233, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B1356]
theorem treeEq1232 : B1232.tree = HexagonCover.NBand.M7100_7300.SplitData.node1232 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1233
  · rfl
  · rfl
  · rfl
  · exact treeEq1356

theorem accepted1232 : B1232.accepted = true := by decide +kernel
theorem checked1232 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1232 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1232]
  exact B1232.sound accepted1232
#print axioms checked1232

def Tip1216_1232 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1232 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1232
def B1223 : Block := .branch 90 ![288230376151712129, 374144419156711147060143317175368453031918731003394, 6148, 24584, 98320, 393248, 1461501664553492272195829302348219637655682940992] ![(.leaf 0 (Common.fact 879).pointIds 879), (.leaf 1 (Common.fact 927).pointIds 927), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq1223 : B1223.tree = HexagonCover.NBand.M7100_7300.SplitData.node1223 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1222 : Block := .branch 160 ![288230376151712129, 374144419156711147060143317175368453031918731003394, 18446745173221185540, 24584, 98320, 393248, 27222589353992144469631936617999750398016] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1223]
theorem treeEq1222 : B1222.tree = HexagonCover.NBand.M7100_7300.SplitData.node1222 := by
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
  · exact treeEq1223

def B1221 : Block := .branch 168 ![288230376151712129, 1538, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 345).pointIds 345), B1222, (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 877).pointIds 877)]
theorem treeEq1221 : B1221.tree = HexagonCover.NBand.M7100_7300.SplitData.node1221 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1222
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1220 : Block := .branch 132 ![288230376151712129, 1538, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B1221]
theorem treeEq1220 : B1220.tree = HexagonCover.NBand.M7100_7300.SplitData.node1220 := by
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
  · exact treeEq1221

def B1219 : Block := .branch 133 ![288230376151712129, 1538, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B1220]
theorem treeEq1219 : B1219.tree = HexagonCover.NBand.M7100_7300.SplitData.node1219 := by
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
  · exact treeEq1220

def B1218 : Block := .branch 157 ![288230376151712129, 1538, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B1219, (.leaf 5 (Common.fact 206).pointIds 206), (.leaf 0 [] 0)]
theorem treeEq1218 : B1218.tree = HexagonCover.NBand.M7100_7300.SplitData.node1218 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1219
  · rfl
  · rfl

def B1217 : Block := .branch 166 ![288230376151712129, 1538, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 196).pointIds 196), (.leaf 1 (Common.fact 197).pointIds 197), (.leaf 2 (Common.fact 198).pointIds 198), (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), B1218, (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1217 : B1217.tree = HexagonCover.NBand.M7100_7300.SplitData.node1217 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1218
  · rfl

def B1231 : Block := .branch 90 ![576460752303423873, 374144419156711147060143317175368453031918731003394, 6148, 24584, 98320, 393248, 1461501664553492272195829302348219637655682940992] ![(.leaf 0 (Common.fact 883).pointIds 883), (.leaf 1 (Common.fact 927).pointIds 927), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq1231 : B1231.tree = HexagonCover.NBand.M7100_7300.SplitData.node1231 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1230 : Block := .branch 160 ![576460752303423873, 374144419156711147060143317175368453031918731003394, 18446745173221185540, 24584, 98320, 393248, 27222589353992144469631936617999750398016] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1231]
theorem treeEq1230 : B1230.tree = HexagonCover.NBand.M7100_7300.SplitData.node1230 := by
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
  · exact treeEq1231

def B1229 : Block := .branch 168 ![576460752303423873, 1538, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 369).pointIds 369), B1230, (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 877).pointIds 877)]
theorem treeEq1229 : B1229.tree = HexagonCover.NBand.M7100_7300.SplitData.node1229 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1230
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1228 : Block := .branch 132 ![576460752303423873, 1538, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B1229]
theorem treeEq1228 : B1228.tree = HexagonCover.NBand.M7100_7300.SplitData.node1228 := by
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
  · exact treeEq1229

def B1227 : Block := .branch 133 ![576460752303423873, 1538, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B1228]
theorem treeEq1227 : B1227.tree = HexagonCover.NBand.M7100_7300.SplitData.node1227 := by
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
  · exact treeEq1228

def B1226 : Block := .branch 157 ![576460752303423873, 1538, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B1227, (.leaf 5 (Common.fact 206).pointIds 206), (.leaf 0 [] 0)]
theorem treeEq1226 : B1226.tree = HexagonCover.NBand.M7100_7300.SplitData.node1226 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1227
  · rfl
  · rfl

def B1225 : Block := .branch 166 ![576460752303423873, 1538, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 882).pointIds 882), (.leaf 1 (Common.fact 197).pointIds 197), (.leaf 2 (Common.fact 198).pointIds 198), (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), B1226, (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1225 : B1225.tree = HexagonCover.NBand.M7100_7300.SplitData.node1225 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1226
  · rfl

def B1224 : Block := .branch 59 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B1225, Tip1216_1232, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq1224 : B1224.tree = HexagonCover.NBand.M7100_7300.SplitData.node1224 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1225
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1216 : Block := .branch 58 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B1217, B1224, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq1216 : B1216.tree = HexagonCover.NBand.M7100_7300.SplitData.node1216 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1217
  · exact treeEq1224
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1216 : B1216.accepted = true := by decide +kernel
theorem checked1216 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1216 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1216]
  exact B1216.sound accepted1216
#print axioms checked1216

def Tip0792_0804 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0804 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0011.checked0804
def Tip0792_0943 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0943 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0013.checked0943
def B0796 : Block := .branch 67 ![385, 180143985094821378, 6148, 24584, 98320, 393248, 5987772208166487327363753888692829474429447087587392] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq0796 : B0796.tree = HexagonCover.NBand.M7100_7300.SplitData.node0796 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0795 : Block := .branch 172 ![385, 180143985094821378, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 1461501659108974401460813886934225918747391557696] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0796]
theorem treeEq0795 : B0795.tree = HexagonCover.NBand.M7100_7300.SplitData.node0795 := by
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
  · exact treeEq0796

def B0794 : Block := .branch 171 ![385, 180143985094821378, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1461501659108974401460813886934225918747391557696] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0795, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 897).pointIds 897)]
theorem treeEq0794 : B0794.tree = HexagonCover.NBand.M7100_7300.SplitData.node0794 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0795
  · rfl
  · rfl

def B0793 : Block := .branch 160 ![385, 180143985094821378, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 893).pointIds 893), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0794]
theorem treeEq0793 : B0793.tree = HexagonCover.NBand.M7100_7300.SplitData.node0793 := by
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
  · exact treeEq0794

def B0800 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0800 : B0800.tree = HexagonCover.NBand.M7100_7300.SplitData.node0800 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0799 : Block := .branch 168 ![288230376151712129, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0800]
theorem treeEq0799 : B0799.tree = HexagonCover.NBand.M7100_7300.SplitData.node0799 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0800

def B0803 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 810).pointIds 810), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0803 : B0803.tree = HexagonCover.NBand.M7100_7300.SplitData.node0803 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0802 : Block := .branch 168 ![576460752303423873, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0803]
theorem treeEq0802 : B0802.tree = HexagonCover.NBand.M7100_7300.SplitData.node0802 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0803

def B0801 : Block := .branch 59 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0802, Tip0792_0804, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0801 : B0801.tree = HexagonCover.NBand.M7100_7300.SplitData.node0801 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0802
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0798 : Block := .branch 58 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0799, B0801, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq0798 : B0798.tree = HexagonCover.NBand.M7100_7300.SplitData.node0798 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0799
  · exact treeEq0801
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0939 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0939 : B0939.tree = HexagonCover.NBand.M7100_7300.SplitData.node0939 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0938 : Block := .branch 168 ![288230376151712129, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0939]
theorem treeEq0938 : B0938.tree = HexagonCover.NBand.M7100_7300.SplitData.node0938 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0939

def B0942 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 810).pointIds 810), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0942 : B0942.tree = HexagonCover.NBand.M7100_7300.SplitData.node0942 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0941 : Block := .branch 168 ![576460752303423873, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0942]
theorem treeEq0941 : B0941.tree = HexagonCover.NBand.M7100_7300.SplitData.node0941 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0942

def B0940 : Block := .branch 59 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0941, Tip0792_0943, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0940 : B0940.tree = HexagonCover.NBand.M7100_7300.SplitData.node0940 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0941
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0937 : Block := .branch 58 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0938, B0940, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq0937 : B0937.tree = HexagonCover.NBand.M7100_7300.SplitData.node0937 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0938
  · exact treeEq0940
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0797 : Block := .branch 56 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 159).pointIds 159), B0798, B0937, (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), (.leaf 6 (Common.fact 163).pointIds 163)]
theorem treeEq0797 : B0797.tree = HexagonCover.NBand.M7100_7300.SplitData.node0797 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0798
  · exact treeEq0937
  · rfl
  · rfl
  · rfl
  · rfl

def B0792 : Block := .branch 55 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 87).pointIds 87), B0793, B0797, (.leaf 3 (Common.fact 88).pointIds 88), (.leaf 4 (Common.fact 89).pointIds 89), (.leaf 5 (Common.fact 90).pointIds 90), (.leaf 6 (Common.fact 91).pointIds 91)]
theorem treeEq0792 : B0792.tree = HexagonCover.NBand.M7100_7300.SplitData.node0792 := by
  change Tree.branch (55 : Fin 173) _ = Tree.branch (55 : Fin 173) _
  apply congrArg (Tree.branch (55 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0793
  · exact treeEq0797
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0792 : B0792.accepted = true := by decide +kernel
theorem checked0792 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0792 (maskNeeds ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0792]
  exact B0792.sound accepted0792
#print axioms checked0792

end HexagonCover.NBand.M7100_7300.SplitTree.Run0017
