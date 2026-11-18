import HexagonCover.N7900.SplitAlignedTree.Run0012
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0013
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip1013_1014 : Block := .tip HexagonCover.N7900.SplitData.node1014 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0012.checked1014
def B1042 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1042 : B1042.tree = HexagonCover.N7900.SplitData.node1042 := by
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

def B1041 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1042]
theorem treeEq1041 : B1041.tree = HexagonCover.N7900.SplitData.node1041 := by
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
  · exact treeEq1042

def B1040 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1041, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1040 : B1040.tree = HexagonCover.N7900.SplitData.node1040 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1041
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1039 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1040, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1039 : B1039.tree = HexagonCover.N7900.SplitData.node1039 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1040
  · rfl
  · rfl

def B1038 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1039, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1038 : B1038.tree = HexagonCover.N7900.SplitData.node1038 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1039
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1037 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1038, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1037 : B1037.tree = HexagonCover.N7900.SplitData.node1037 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1038
  · rfl

def B1036 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1037, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1036 : B1036.tree = HexagonCover.N7900.SplitData.node1036 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1037
  · rfl
  · rfl

def B1035 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1036]
theorem treeEq1035 : B1035.tree = HexagonCover.N7900.SplitData.node1035 := by
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
  · exact treeEq1036

def B1044 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1044 : B1044.tree = HexagonCover.N7900.SplitData.node1044 := by
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

def B1043 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1044, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1043 : B1043.tree = HexagonCover.N7900.SplitData.node1043 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1044
  · rfl
  · rfl

def B1034 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1035, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1043]
theorem treeEq1034 : B1034.tree = HexagonCover.N7900.SplitData.node1034 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1035
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1043

def B1051 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1051 : B1051.tree = HexagonCover.N7900.SplitData.node1051 := by
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

def B1050 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1051]
theorem treeEq1050 : B1050.tree = HexagonCover.N7900.SplitData.node1050 := by
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
  · exact treeEq1051

def B1049 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1050, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1049 : B1049.tree = HexagonCover.N7900.SplitData.node1049 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1050
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1048 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1049, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1048 : B1048.tree = HexagonCover.N7900.SplitData.node1048 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1049
  · rfl
  · rfl

def B1047 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1048, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1047 : B1047.tree = HexagonCover.N7900.SplitData.node1047 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1048
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1046 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1047, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1046 : B1046.tree = HexagonCover.N7900.SplitData.node1046 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1047
  · rfl

def B1045 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1046, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1045 : B1045.tree = HexagonCover.N7900.SplitData.node1045 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1046
  · rfl
  · rfl

def B1033 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B1034, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1045]
theorem treeEq1033 : B1033.tree = HexagonCover.N7900.SplitData.node1033 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1034
  · rfl
  · rfl
  · rfl
  · exact treeEq1045

def B1013 : Block := .branch 74 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip1013_1014, B1033, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq1013 : B1013.tree = HexagonCover.N7900.SplitData.node1013 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1033
  · rfl
  · rfl
  · rfl

theorem accepted1013 : B1013.accepted = true := by decide +kernel
theorem checked1013 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1013 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1013]
  exact B1013.sound accepted1013
#print axioms checked1013

def B1069 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1069 : B1069.tree = HexagonCover.N7900.SplitData.node1069 := by
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

def B1068 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1069]
theorem treeEq1068 : B1068.tree = HexagonCover.N7900.SplitData.node1068 := by
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
  · exact treeEq1069

def B1067 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1068, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1067 : B1067.tree = HexagonCover.N7900.SplitData.node1067 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1068
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1066 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1067, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1066 : B1066.tree = HexagonCover.N7900.SplitData.node1066 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1067
  · rfl
  · rfl

def B1065 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1066, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1065 : B1065.tree = HexagonCover.N7900.SplitData.node1065 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1066
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1064 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1065, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1064 : B1064.tree = HexagonCover.N7900.SplitData.node1064 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1065
  · rfl

def B1063 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1064, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1063 : B1063.tree = HexagonCover.N7900.SplitData.node1063 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1064
  · rfl
  · rfl

def B1062 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1063]
theorem treeEq1062 : B1062.tree = HexagonCover.N7900.SplitData.node1062 := by
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
  · exact treeEq1063

def B1071 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1071 : B1071.tree = HexagonCover.N7900.SplitData.node1071 := by
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

def B1070 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1071, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1070 : B1070.tree = HexagonCover.N7900.SplitData.node1070 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1071
  · rfl
  · rfl

def B1061 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1062, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1070]
theorem treeEq1061 : B1061.tree = HexagonCover.N7900.SplitData.node1061 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1062
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1070

def B1078 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1078 : B1078.tree = HexagonCover.N7900.SplitData.node1078 := by
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

def B1077 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1078]
theorem treeEq1077 : B1077.tree = HexagonCover.N7900.SplitData.node1077 := by
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
  · exact treeEq1078

def B1076 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1077, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1076 : B1076.tree = HexagonCover.N7900.SplitData.node1076 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1077
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1075 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1076, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1075 : B1075.tree = HexagonCover.N7900.SplitData.node1075 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1076
  · rfl
  · rfl

def B1074 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1075, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1074 : B1074.tree = HexagonCover.N7900.SplitData.node1074 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1075
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1073 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1074, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1073 : B1073.tree = HexagonCover.N7900.SplitData.node1073 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1074
  · rfl

def B1072 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1073, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1072 : B1072.tree = HexagonCover.N7900.SplitData.node1072 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1073
  · rfl
  · rfl

def B1060 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B1061, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1072]
theorem treeEq1060 : B1060.tree = HexagonCover.N7900.SplitData.node1060 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1061
  · rfl
  · rfl
  · rfl
  · exact treeEq1072

theorem accepted1060 : B1060.accepted = true := by decide +kernel
theorem checked1060 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1060 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1060]
  exact B1060.sound accepted1060
#print axioms checked1060

def B1108 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1108 : B1108.tree = HexagonCover.N7900.SplitData.node1108 := by
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

def B1107 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1108]
theorem treeEq1107 : B1107.tree = HexagonCover.N7900.SplitData.node1107 := by
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
  · exact treeEq1108

def B1106 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1107, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1106 : B1106.tree = HexagonCover.N7900.SplitData.node1106 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1107
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1105 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1106, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1105 : B1105.tree = HexagonCover.N7900.SplitData.node1105 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1106
  · rfl
  · rfl

def B1104 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1105, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1104 : B1104.tree = HexagonCover.N7900.SplitData.node1104 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1105
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1103 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1104, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1103 : B1103.tree = HexagonCover.N7900.SplitData.node1103 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1104
  · rfl

def B1102 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1103, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1102 : B1102.tree = HexagonCover.N7900.SplitData.node1102 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1103
  · rfl
  · rfl

def B1101 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1102]
theorem treeEq1101 : B1101.tree = HexagonCover.N7900.SplitData.node1101 := by
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
  · exact treeEq1102

def B1110 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1110 : B1110.tree = HexagonCover.N7900.SplitData.node1110 := by
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

def B1109 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1110, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1109 : B1109.tree = HexagonCover.N7900.SplitData.node1109 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1110
  · rfl
  · rfl

def B1100 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1101, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1109]
theorem treeEq1100 : B1100.tree = HexagonCover.N7900.SplitData.node1100 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1101
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1109

def B1117 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1117 : B1117.tree = HexagonCover.N7900.SplitData.node1117 := by
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

def B1116 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1117]
theorem treeEq1116 : B1116.tree = HexagonCover.N7900.SplitData.node1116 := by
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
  · exact treeEq1117

def B1115 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1116, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1115 : B1115.tree = HexagonCover.N7900.SplitData.node1115 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1116
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1114 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1115, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1114 : B1114.tree = HexagonCover.N7900.SplitData.node1114 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1115
  · rfl
  · rfl

def B1113 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1114, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1113 : B1113.tree = HexagonCover.N7900.SplitData.node1113 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1114
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1112 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1113, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1112 : B1112.tree = HexagonCover.N7900.SplitData.node1112 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1113
  · rfl

def B1111 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1112, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1111 : B1111.tree = HexagonCover.N7900.SplitData.node1111 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1112
  · rfl
  · rfl

def B1099 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B1100, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1111]
theorem treeEq1099 : B1099.tree = HexagonCover.N7900.SplitData.node1099 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1100
  · rfl
  · rfl
  · rfl
  · exact treeEq1111

theorem accepted1099 : B1099.accepted = true := by decide +kernel
theorem checked1099 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1099 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1099]
  exact B1099.sound accepted1099
#print axioms checked1099

def Tip1059_1060 : Block := .tip HexagonCover.N7900.SplitData.node1060 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1060
def B1088 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1088 : B1088.tree = HexagonCover.N7900.SplitData.node1088 := by
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

def B1087 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1088]
theorem treeEq1087 : B1087.tree = HexagonCover.N7900.SplitData.node1087 := by
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
  · exact treeEq1088

def B1086 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1087, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1086 : B1086.tree = HexagonCover.N7900.SplitData.node1086 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1087
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1085 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1086, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1085 : B1085.tree = HexagonCover.N7900.SplitData.node1085 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1086
  · rfl
  · rfl

def B1084 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1085, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1084 : B1084.tree = HexagonCover.N7900.SplitData.node1084 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1085
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1083 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1084, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1083 : B1083.tree = HexagonCover.N7900.SplitData.node1083 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1084
  · rfl

def B1082 : Block := .branch 142 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1083, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1082 : B1082.tree = HexagonCover.N7900.SplitData.node1082 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1083
  · rfl
  · rfl

def B1081 : Block := .branch 88 ![10394734921872071388083324989735297, 302231599159582857889282, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 535).pointIds 535), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1082]
theorem treeEq1081 : B1081.tree = HexagonCover.N7900.SplitData.node1081 := by
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
  · exact treeEq1082

def B1090 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1090 : B1090.tree = HexagonCover.N7900.SplitData.node1090 := by
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

def B1089 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1090, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1089 : B1089.tree = HexagonCover.N7900.SplitData.node1089 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1090
  · rfl
  · rfl

def B1080 : Block := .branch 78 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1081, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1089]
theorem treeEq1080 : B1080.tree = HexagonCover.N7900.SplitData.node1080 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1081
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1089

def B1097 : Block := .branch 100 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1097 : B1097.tree = HexagonCover.N7900.SplitData.node1097 := by
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

def B1096 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1097]
theorem treeEq1096 : B1096.tree = HexagonCover.N7900.SplitData.node1096 := by
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
  · exact treeEq1097

def B1095 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1096, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1095 : B1095.tree = HexagonCover.N7900.SplitData.node1095 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1096
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1094 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1095, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1094 : B1094.tree = HexagonCover.N7900.SplitData.node1094 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1095
  · rfl
  · rfl

def B1093 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1094, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1093 : B1093.tree = HexagonCover.N7900.SplitData.node1093 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1094
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1092 : Block := .branch 169 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1093, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1092 : B1092.tree = HexagonCover.N7900.SplitData.node1092 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1093
  · rfl

def B1091 : Block := .branch 143 ![10394734921872071388083324989735297, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1092, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1091 : B1091.tree = HexagonCover.N7900.SplitData.node1091 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1092
  · rfl
  · rfl

def B1079 : Block := .branch 76 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 551).pointIds 551), B1080, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1091]
theorem treeEq1079 : B1079.tree = HexagonCover.N7900.SplitData.node1079 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1080
  · rfl
  · rfl
  · rfl
  · exact treeEq1091

def B1059 : Block := .branch 74 ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip1059_1060, B1079, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq1059 : B1059.tree = HexagonCover.N7900.SplitData.node1059 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1079
  · rfl
  · rfl
  · rfl

theorem accepted1059 : B1059.accepted = true := by decide +kernel
theorem checked1059 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1059 (maskNeeds ![10394734921872071388083324989735297, 442866113694593451522, 9295429630892709892, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1059]
  exact B1059.sound accepted1059
#print axioms checked1059

end HexagonCover.N7900.SplitAlignedTree.Run0013
