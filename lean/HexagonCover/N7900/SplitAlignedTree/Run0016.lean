import HexagonCover.N7900.SplitAlignedTree.Run0013
import HexagonCover.N7900.SplitAlignedTree.Run0014
import HexagonCover.N7900.SplitAlignedTree.Run0015
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0016
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip1224_1225 : Block := .tip HexagonCover.N7900.SplitData.node1225 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0015.checked1225
def B1253 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1253 : B1253.tree = HexagonCover.N7900.SplitData.node1253 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1252 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1253]
theorem treeEq1252 : B1252.tree = HexagonCover.N7900.SplitData.node1252 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1253

def B1251 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1252, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1251 : B1251.tree = HexagonCover.N7900.SplitData.node1251 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1252
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1250 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1251, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1250 : B1250.tree = HexagonCover.N7900.SplitData.node1250 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1251
  · rfl
  · rfl

def B1249 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1250, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1249 : B1249.tree = HexagonCover.N7900.SplitData.node1249 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1250
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1248 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1249, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1248 : B1248.tree = HexagonCover.N7900.SplitData.node1248 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1249
  · rfl

def B1247 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1248, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1247 : B1247.tree = HexagonCover.N7900.SplitData.node1247 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1248
  · rfl
  · rfl

def B1246 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1247]
theorem treeEq1246 : B1246.tree = HexagonCover.N7900.SplitData.node1246 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1247

def B1255 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1255 : B1255.tree = HexagonCover.N7900.SplitData.node1255 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1254 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1255, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1254 : B1254.tree = HexagonCover.N7900.SplitData.node1254 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1255
  · rfl
  · rfl

def B1245 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1246, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1254]
theorem treeEq1245 : B1245.tree = HexagonCover.N7900.SplitData.node1245 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1246
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1254

def B1262 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1262 : B1262.tree = HexagonCover.N7900.SplitData.node1262 := by
  change Tree.branch (100 : Fin 170) _ = Tree.branch (100 : Fin 170) _
  apply congrArg (Tree.branch (100 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1261 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1262]
theorem treeEq1261 : B1261.tree = HexagonCover.N7900.SplitData.node1261 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1262

def B1260 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1261, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1260 : B1260.tree = HexagonCover.N7900.SplitData.node1260 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1261
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1259 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1260, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1259 : B1259.tree = HexagonCover.N7900.SplitData.node1259 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1260
  · rfl
  · rfl

def B1258 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1259, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1258 : B1258.tree = HexagonCover.N7900.SplitData.node1258 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1259
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1257 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1258, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1257 : B1257.tree = HexagonCover.N7900.SplitData.node1257 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1258
  · rfl

def B1256 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1257, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1256 : B1256.tree = HexagonCover.N7900.SplitData.node1256 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1257
  · rfl
  · rfl

def B1244 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B1245, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1256]
theorem treeEq1244 : B1244.tree = HexagonCover.N7900.SplitData.node1244 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1245
  · rfl
  · rfl
  · rfl
  · exact treeEq1256

def B1224 : Block := .branch 74 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip1224_1225, B1244, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq1224 : B1224.tree = HexagonCover.N7900.SplitData.node1224 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1244
  · rfl
  · rfl
  · rfl

theorem accepted1224 : B1224.accepted = true := by decide +kernel
theorem checked1224 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1224 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1224]
  exact B1224.sound accepted1224
#print axioms checked1224

def Tip1263_1264 : Block := .tip HexagonCover.N7900.SplitData.node1264 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0015.checked1264
def B1292 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1292 : B1292.tree = HexagonCover.N7900.SplitData.node1292 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1291 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1292]
theorem treeEq1291 : B1291.tree = HexagonCover.N7900.SplitData.node1291 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1292

def B1290 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1291, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1290 : B1290.tree = HexagonCover.N7900.SplitData.node1290 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1291
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1289 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1290, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1289 : B1289.tree = HexagonCover.N7900.SplitData.node1289 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1290
  · rfl
  · rfl

def B1288 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1289, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1288 : B1288.tree = HexagonCover.N7900.SplitData.node1288 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1289
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1287 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1288, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1287 : B1287.tree = HexagonCover.N7900.SplitData.node1287 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1288
  · rfl

def B1286 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1287, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1286 : B1286.tree = HexagonCover.N7900.SplitData.node1286 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1287
  · rfl
  · rfl

def B1285 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1286]
theorem treeEq1285 : B1285.tree = HexagonCover.N7900.SplitData.node1285 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1286

def B1294 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1294 : B1294.tree = HexagonCover.N7900.SplitData.node1294 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1293 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1294, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1293 : B1293.tree = HexagonCover.N7900.SplitData.node1293 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1294
  · rfl
  · rfl

def B1284 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1285, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1293]
theorem treeEq1284 : B1284.tree = HexagonCover.N7900.SplitData.node1284 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1285
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1293

def B1301 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1301 : B1301.tree = HexagonCover.N7900.SplitData.node1301 := by
  change Tree.branch (100 : Fin 170) _ = Tree.branch (100 : Fin 170) _
  apply congrArg (Tree.branch (100 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1300 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1301]
theorem treeEq1300 : B1300.tree = HexagonCover.N7900.SplitData.node1300 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1301

def B1299 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1300, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1299 : B1299.tree = HexagonCover.N7900.SplitData.node1299 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1300
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1298 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1299, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1298 : B1298.tree = HexagonCover.N7900.SplitData.node1298 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1299
  · rfl
  · rfl

def B1297 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1298, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1297 : B1297.tree = HexagonCover.N7900.SplitData.node1297 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1298
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1296 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1297, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1296 : B1296.tree = HexagonCover.N7900.SplitData.node1296 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1297
  · rfl

def B1295 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1296, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1295 : B1295.tree = HexagonCover.N7900.SplitData.node1295 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1296
  · rfl
  · rfl

def B1283 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B1284, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1295]
theorem treeEq1283 : B1283.tree = HexagonCover.N7900.SplitData.node1283 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1284
  · rfl
  · rfl
  · rfl
  · exact treeEq1295

def B1263 : Block := .branch 74 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip1263_1264, B1283, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq1263 : B1263.tree = HexagonCover.N7900.SplitData.node1263 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1283
  · rfl
  · rfl
  · rfl

theorem accepted1263 : B1263.accepted = true := by decide +kernel
theorem checked1263 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1263 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1263]
  exact B1263.sound accepted1263
#print axioms checked1263

def Tip0885_1059 : Block := .tip HexagonCover.N7900.SplitData.node1059 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0013.checked1059
def Tip0885_1098 : Block := .tip HexagonCover.N7900.SplitData.node1098 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0014.checked1098
def Tip0885_0887 : Block := .tip HexagonCover.N7900.SplitData.node0887 ![10141204802416131022332331295105, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0014.checked0887
def Tip0885_1145 : Block := .tip HexagonCover.N7900.SplitData.node1145 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0015.checked1145
def Tip0885_1184 : Block := .tip HexagonCover.N7900.SplitData.node1184 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0015.checked1184
def Tip0885_1224 : Block := .tip HexagonCover.N7900.SplitData.node1224 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1224
def Tip0885_1263 : Block := .tip HexagonCover.N7900.SplitData.node1263 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1263
def B1058 : Block := .branch 73 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip0885_1059, Tip0885_1098, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1058 : B1058.tree = HexagonCover.N7900.SplitData.node1058 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1138 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1138 : B1138.tree = HexagonCover.N7900.SplitData.node1138 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1137 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1138, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1137 : B1137.tree = HexagonCover.N7900.SplitData.node1137 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1138
  · rfl
  · rfl

def B1057 : Block := .branch 68 ![10394734921872071388083324989735297, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 659).pointIds 659), B1058, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B1137]
theorem treeEq1057 : B1057.tree = HexagonCover.N7900.SplitData.node1057 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1058
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1137

def B1056 : Block := .branch 113 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1057, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1056 : B1056.tree = HexagonCover.N7900.SplitData.node1056 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1057
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1055 : Block := .branch 144 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1056, (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1055 : B1055.tree = HexagonCover.N7900.SplitData.node1055 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1056
  · rfl

def B1054 : Block := .branch 161 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38690348594151003235835912, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 625).pointIds 625), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B1055]
theorem treeEq1054 : B1054.tree = HexagonCover.N7900.SplitData.node1054 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1055

def B0886 : Block := .branch 72 ![10141204802416131022332331295105, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), Tip0885_0887, B1054, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq0886 : B0886.tree = HexagonCover.N7900.SplitData.node0886 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1054
  · rfl
  · rfl
  · rfl

def B1144 : Block := .branch 73 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip0885_1145, Tip0885_1184, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1144 : B1144.tree = HexagonCover.N7900.SplitData.node1144 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1223 : Block := .branch 73 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip0885_1224, Tip0885_1263, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1223 : B1223.tree = HexagonCover.N7900.SplitData.node1223 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1143 : Block := .branch 72 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), B1144, B1223, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq1143 : B1143.tree = HexagonCover.N7900.SplitData.node1143 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1144
  · exact treeEq1223
  · rfl
  · rfl
  · rfl

def B1303 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1303 : B1303.tree = HexagonCover.N7900.SplitData.node1303 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1302 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1303, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1302 : B1302.tree = HexagonCover.N7900.SplitData.node1302 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1303
  · rfl
  · rfl

def B1142 : Block := .branch 68 ![10394734921872071388083324989735297, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 659).pointIds 659), B1143, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B1302]
theorem treeEq1142 : B1142.tree = HexagonCover.N7900.SplitData.node1142 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1143
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1302

def B1141 : Block := .branch 113 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1142, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1141 : B1141.tree = HexagonCover.N7900.SplitData.node1141 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1142
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1140 : Block := .branch 144 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1141, (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1140 : B1140.tree = HexagonCover.N7900.SplitData.node1140 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1141
  · rfl

def B1139 : Block := .branch 161 ![10141204802416131022332331295105, 147718208515240625666, 9295429630892709892, 38687987410909568413229064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 625).pointIds 625), (.leaf 3 (Common.fact 676).pointIds 676), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B1140]
theorem treeEq1139 : B1139.tree = HexagonCover.N7900.SplitData.node1139 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1140

def B0885 : Block := .branch 71 ![10141204802416131022332331295105, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), B0886, B1139, (.leaf 4 (Common.fact 322).pointIds 322), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 0 [] 0)]
theorem treeEq0885 : B0885.tree = HexagonCover.N7900.SplitData.node0885 := by
  change Tree.branch (71 : Fin 170) _ = Tree.branch (71 : Fin 170) _
  apply congrArg (Tree.branch (71 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0886
  · exact treeEq1139
  · rfl
  · rfl
  · rfl

theorem accepted0885 : B0885.accepted = true := by decide +kernel
theorem checked0885 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0885 (maskNeeds ![10141204802416131022332331295105, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0885]
  exact B0885.sound accepted0885
#print axioms checked0885

def Tip0882_0885 : Block := .tip HexagonCover.N7900.SplitData.node0885 ![10141204802416131022332331295105, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0885
def B1305 : Block := .branch 133 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 164).pointIds 164), (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq1305 : B1305.tree = HexagonCover.N7900.SplitData.node1305 := by
  change Tree.branch (133 : Fin 170) _ = Tree.branch (133 : Fin 170) _
  apply congrArg (Tree.branch (133 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1304 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B1305, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 506).pointIds 506)]
theorem treeEq1304 : B1304.tree = HexagonCover.N7900.SplitData.node1304 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1305
  · rfl
  · rfl

def B0884 : Block := .branch 69 ![10141204801825835211973625643393, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![Tip0882_0885, (.leaf 1 (Common.fact 543).pointIds 543), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 425).pointIds 425), (.leaf 4 (Common.fact 426).pointIds 426), (.leaf 5 (Common.fact 427).pointIds 427), B1304]
theorem treeEq0884 : B0884.tree = HexagonCover.N7900.SplitData.node0884 := by
  change Tree.branch (69 : Fin 170) _ = Tree.branch (69 : Fin 170) _
  apply congrArg (Tree.branch (69 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1304

def B1308 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 512).pointIds 512)]
theorem treeEq1308 : B1308.tree = HexagonCover.N7900.SplitData.node1308 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1307 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1308, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 510).pointIds 510)]
theorem treeEq1307 : B1307.tree = HexagonCover.N7900.SplitData.node1307 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1308
  · rfl
  · rfl

def B1306 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1307, (.leaf 6 (Common.fact 509).pointIds 509)]
theorem treeEq1306 : B1306.tree = HexagonCover.N7900.SplitData.node1306 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1307
  · rfl

def B0883 : Block := .branch 67 ![10141204801825835211973625643393, 720716677867636226, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 106).pointIds 106), B0884, (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B1306]
theorem treeEq0883 : B0883.tree = HexagonCover.N7900.SplitData.node0883 := by
  change Tree.branch (67 : Fin 170) _ = Tree.branch (67 : Fin 170) _
  apply congrArg (Tree.branch (67 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0884
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1306

def B1311 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq1311 : B1311.tree = HexagonCover.N7900.SplitData.node1311 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1310 : Block := .branch 168 ![385, 1461501637330902918203684832716859480408235968002, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![B1311, (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 591).pointIds 591), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1310 : B1310.tree = HexagonCover.N7900.SplitData.node1310 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1311
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1309 : Block := .branch 160 ![385, 576460752303425026, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 334).pointIds 334), B1310, (.leaf 2 (Common.fact 596).pointIds 596), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1309 : B1309.tree = HexagonCover.N7900.SplitData.node1309 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1310
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0882 : Block := .branch 65 ![10141204801825835211973625643393, 1008947054019347970, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 225).pointIds 225), (.leaf 1 (Common.fact 542).pointIds 542), B0883, (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B1309]
theorem treeEq0882 : B0882.tree = HexagonCover.N7900.SplitData.node0882 := by
  change Tree.branch (65 : Fin 170) _ = Tree.branch (65 : Fin 170) _
  apply congrArg (Tree.branch (65 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0883
  · rfl
  · rfl
  · rfl
  · exact treeEq1309

theorem accepted0882 : B0882.accepted = true := by decide +kernel
theorem checked0882 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0882 (maskNeeds ![10141204801825835211973625643393, 1008947054019347970, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0882]
  exact B0882.sound accepted0882
#print axioms checked0882

def Tip0871_0882 : Block := .tip HexagonCover.N7900.SplitData.node0882 ![10141204801825835211973625643393, 1008947054019347970, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0882
def B0881 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 540).pointIds 540)]
theorem treeEq0881 : B0881.tree = HexagonCover.N7900.SplitData.node0881 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0880 : Block := .branch 169 ![10141204801825835211973625643393, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), B0881, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0880 : B0880.tree = HexagonCover.N7900.SplitData.node0880 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0881
  · rfl
  · rfl

def B0879 : Block := .branch 166 ![10141204801826411672725929066881, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 201).pointIds 201), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0880, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0879 : B0879.tree = HexagonCover.N7900.SplitData.node0879 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0880
  · rfl

def B0878 : Block := .branch 88 ![10141204801826411672725929066881, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0879]
theorem treeEq0878 : B0878.tree = HexagonCover.N7900.SplitData.node0878 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0879

def B0877 : Block := .branch 78 ![10141204801826411672725929066881, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 194).pointIds 194), B0878, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0877 : B0877.tree = HexagonCover.N7900.SplitData.node0877 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0878
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0876 : Block := .branch 133 ![10141204801826411672725929066881, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0877]
theorem treeEq0876 : B0876.tree = HexagonCover.N7900.SplitData.node0876 := by
  change Tree.branch (133 : Fin 170) _ = Tree.branch (133 : Fin 170) _
  apply congrArg (Tree.branch (133 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0877

def B0875 : Block := .branch 138 ![10141204801826411672725929066881, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0876, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0875 : B0875.tree = HexagonCover.N7900.SplitData.node0875 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0876
  · rfl
  · rfl

def B0874 : Block := .branch 144 ![10141204801826411672725929066881, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0875, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0874 : B0874.tree = HexagonCover.N7900.SplitData.node0874 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0875
  · rfl

def B0873 : Block := .branch 124 ![10141204801826411672725929066881, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0874]
theorem treeEq0873 : B0873.tree = HexagonCover.N7900.SplitData.node0873 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0874

def B0872 : Block := .branch 59 ![10141204801825835211973625643393, 432486301715924482, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0873, Tip0871_0882, (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 190).pointIds 190)]
theorem treeEq0872 : B0872.tree = HexagonCover.N7900.SplitData.node0872 := by
  change Tree.branch (59 : Fin 170) _ = Tree.branch (59 : Fin 170) _
  apply congrArg (Tree.branch (59 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0873
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0871 : Block := .branch 64 ![10141204801825835211973625643393, 432486301715924482, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 166).pointIds 166), (.leaf 1 (Common.fact 541).pointIds 541), B0872, (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq0871 : B0871.tree = HexagonCover.N7900.SplitData.node0871 := by
  change Tree.branch (64 : Fin 170) _ = Tree.branch (64 : Fin 170) _
  apply congrArg (Tree.branch (64 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0872
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0871 : B0871.accepted = true := by decide +kernel
theorem checked0871 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0871 (maskNeeds ![10141204801825835211973625643393, 432486301715924482, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0871]
  exact B0871.sound accepted0871
#print axioms checked0871

end HexagonCover.N7900.SplitAlignedTree.Run0016
