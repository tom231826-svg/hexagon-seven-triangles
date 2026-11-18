import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0032
import HexagonCover.NBand.M8300_8500.SplitTree.Run0057
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0064
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0024_2132 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2132 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0032.checked2132
def Tip0024_0026 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0026 ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0032.checked0026
def Tip0024_2378 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2378 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0057.checked2378
def B2131 : Block := .branch 118 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), Tip0024_2132, (.leaf 4 (Common.fact 814).pointIds 814), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq2131 : B2131.tree = HexagonCover.NBand.M8300_8500.SplitData.node2131 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2130 : Block := .branch 128 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B2131, (.leaf 4 (Common.fact 813).pointIds 813), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2130 : B2130.tree = HexagonCover.NBand.M8300_8500.SplitData.node2130 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2131
  · rfl
  · rfl
  · rfl

def B2129 : Block := .branch 120 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B2130, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq2129 : B2129.tree = HexagonCover.NBand.M8300_8500.SplitData.node2129 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2130
  · rfl
  · rfl

def B2128 : Block := .branch 143 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B2129]
theorem treeEq2128 : B2128.tree = HexagonCover.NBand.M8300_8500.SplitData.node2128 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2129

def B2127 : Block := .branch 140 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B2128, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq2127 : B2127.tree = HexagonCover.NBand.M8300_8500.SplitData.node2127 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2128
  · rfl
  · rfl

def B2126 : Block := .branch 148 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B2127, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq2126 : B2126.tree = HexagonCover.NBand.M8300_8500.SplitData.node2126 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2127
  · rfl
  · rfl

def B2125 : Block := .branch 168 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 943).pointIds 943), (.leaf 1 (Common.fact 944).pointIds 944), (.leaf 2 (Common.fact 945).pointIds 945), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B2126]
theorem treeEq2125 : B2125.tree = HexagonCover.NBand.M8300_8500.SplitData.node2125 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2126

def B0025 : Block := .branch 65 ![578712552117109121, 540432505040274946, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 143).pointIds 143), Tip0024_0026, B2125, (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 147).pointIds 147)]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M8300_8500.SplitData.node0025 := by
  change Tree.branch (65 : Fin 177) _ = Tree.branch (65 : Fin 177) _
  apply congrArg (Tree.branch (65 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2125
  · rfl
  · rfl
  · rfl
  · rfl

def B2377 : Block := .branch 118 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), Tip0024_2378, (.leaf 4 (Common.fact 814).pointIds 814), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq2377 : B2377.tree = HexagonCover.NBand.M8300_8500.SplitData.node2377 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2376 : Block := .branch 128 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B2377, (.leaf 4 (Common.fact 813).pointIds 813), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2376 : B2376.tree = HexagonCover.NBand.M8300_8500.SplitData.node2376 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2377
  · rfl
  · rfl
  · rfl

def B2375 : Block := .branch 120 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B2376, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq2375 : B2375.tree = HexagonCover.NBand.M8300_8500.SplitData.node2375 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2376
  · rfl
  · rfl

def B2374 : Block := .branch 143 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B2375]
theorem treeEq2374 : B2374.tree = HexagonCover.NBand.M8300_8500.SplitData.node2374 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2375

def B2373 : Block := .branch 140 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B2374, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq2373 : B2373.tree = HexagonCover.NBand.M8300_8500.SplitData.node2373 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2374
  · rfl
  · rfl

def B2372 : Block := .branch 148 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B2373, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq2372 : B2372.tree = HexagonCover.NBand.M8300_8500.SplitData.node2372 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2373
  · rfl
  · rfl

def B2371 : Block := .branch 168 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 980).pointIds 980), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B2372]
theorem treeEq2371 : B2371.tree = HexagonCover.NBand.M8300_8500.SplitData.node2371 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2372

def B0024 : Block := .branch 59 ![2251799813685633, 540432505040274946, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![B0025, B2371, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M8300_8500.SplitData.node0024 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0025
  · exact treeEq2371
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0024 : B0024.accepted = true := by decide +kernel
theorem checked0024 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0024 (maskNeeds ![2251799813685633, 540432505040274946, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0024]
  exact B0024.sound accepted0024
#print axioms checked0024

def B4673 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4673 : B4673.tree = HexagonCover.NBand.M8300_8500.SplitData.node4673 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4672 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B4673, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq4672 : B4672.tree = HexagonCover.NBand.M8300_8500.SplitData.node4672 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4673
  · rfl
  · rfl

def B4671 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B4672, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq4671 : B4671.tree = HexagonCover.NBand.M8300_8500.SplitData.node4671 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4672
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4670 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B4671, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4670 : B4670.tree = HexagonCover.NBand.M8300_8500.SplitData.node4670 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4671
  · rfl
  · rfl
  · rfl
  · rfl

def B4669 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B4670]
theorem treeEq4669 : B4669.tree = HexagonCover.NBand.M8300_8500.SplitData.node4669 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4670

def B4668 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90945226513406734606392204534210411307827216, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4669, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4668 : B4668.tree = HexagonCover.NBand.M8300_8500.SplitData.node4668 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4669
  · rfl

def B4667 : Block := .branch 138 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596777369679693619805708936200280659296272, 233840261972944466912589573234605283144949207269408, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B4668, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4667 : B4667.tree = HexagonCover.NBand.M8300_8500.SplitData.node4667 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4668
  · rfl
  · rfl

def B4666 : Block := .branch 165 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 187072209578355573530071658587684226515959365894176, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B4667, (.leaf 0 [] 0)]
theorem treeEq4666 : B4666.tree = HexagonCover.NBand.M8300_8500.SplitData.node4666 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4667
  · rfl

def B4665 : Block := .branch 167 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B4666, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4665 : B4665.tree = HexagonCover.NBand.M8300_8500.SplitData.node4665 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4666
  · rfl

def B4664 : Block := .branch 146 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B4665, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4664 : B4664.tree = HexagonCover.NBand.M8300_8500.SplitData.node4664 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4665
  · rfl
  · rfl

def B4663 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4664, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4663 : B4663.tree = HexagonCover.NBand.M8300_8500.SplitData.node4663 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4664
  · rfl
  · rfl
  · rfl

theorem accepted4663 : B4663.accepted = true := by decide +kernel
theorem checked4663 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4663 (maskNeeds ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496]) := by
  rw [← treeEq4663]
  exact B4663.sound accepted4663
#print axioms checked4663

def Tip4652_4663 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4663 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496] checked4663
def B4662 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq4662 : B4662.tree = HexagonCover.NBand.M8300_8500.SplitData.node4662 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4661 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4662, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq4661 : B4661.tree = HexagonCover.NBand.M8300_8500.SplitData.node4661 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4662
  · rfl
  · rfl

def B4660 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B4661, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4660 : B4660.tree = HexagonCover.NBand.M8300_8500.SplitData.node4660 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4661
  · rfl
  · rfl

def B4659 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B4660, (.leaf 0 [] 0)]
theorem treeEq4659 : B4659.tree = HexagonCover.NBand.M8300_8500.SplitData.node4659 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4660
  · rfl

def B4658 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B4659, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4658 : B4658.tree = HexagonCover.NBand.M8300_8500.SplitData.node4658 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4659
  · rfl

def B4657 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B4658, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4657 : B4657.tree = HexagonCover.NBand.M8300_8500.SplitData.node4657 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4658
  · rfl
  · rfl

def B4656 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 577).pointIds 577), B4657, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq4656 : B4656.tree = HexagonCover.NBand.M8300_8500.SplitData.node4656 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4657
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4655 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B4656, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq4655 : B4655.tree = HexagonCover.NBand.M8300_8500.SplitData.node4655 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4656
  · rfl
  · rfl
  · rfl
  · rfl

def B4654 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4655, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4654 : B4654.tree = HexagonCover.NBand.M8300_8500.SplitData.node4654 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4655
  · rfl
  · rfl
  · rfl

def B4653 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 42535295865117307932921825928971419680, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B4654]
theorem treeEq4653 : B4653.tree = HexagonCover.NBand.M8300_8500.SplitData.node4653 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4654

def B4652 : Block := .branch 125 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4653, Tip4652_4663]
theorem treeEq4652 : B4652.tree = HexagonCover.NBand.M8300_8500.SplitData.node4652 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4653
  · rfl

theorem accepted4652 : B4652.accepted = true := by decide +kernel
theorem checked4652 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4652 (maskNeeds ![576460752303423873, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4652]
  exact B4652.sound accepted4652
#print axioms checked4652

def B4714 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4714 : B4714.tree = HexagonCover.NBand.M8300_8500.SplitData.node4714 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4713 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B4714, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq4713 : B4713.tree = HexagonCover.NBand.M8300_8500.SplitData.node4713 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4714
  · rfl
  · rfl

def B4712 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B4713, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq4712 : B4712.tree = HexagonCover.NBand.M8300_8500.SplitData.node4712 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4713
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4711 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B4712, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4711 : B4711.tree = HexagonCover.NBand.M8300_8500.SplitData.node4711 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4712
  · rfl
  · rfl
  · rfl
  · rfl

def B4710 : Block := .branch 166 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783604371601068346665977420085189194389389376] ![B4711, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq4710 : B4710.tree = HexagonCover.NBand.M8300_8500.SplitData.node4710 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4711
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4709 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 625).pointIds 625), B4710]
theorem treeEq4709 : B4709.tree = HexagonCover.NBand.M8300_8500.SplitData.node4709 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4710

def B4708 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90945226513406734606392204534210411307827216, 233840261972944508450964441513226311388919841030176, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4709, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4708 : B4708.tree = HexagonCover.NBand.M8300_8500.SplitData.node4708 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4709
  · rfl

def B4707 : Block := .branch 138 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596777369679693619805708936200280659296272, 233840261972944508450964441513226311388919841030176, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B4708, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4707 : B4707.tree = HexagonCover.NBand.M8300_8500.SplitData.node4707 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4708
  · rfl
  · rfl

def B4706 : Block := .branch 165 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 187072209578355615068446526866305254759929999654944, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B4707, (.leaf 0 [] 0)]
theorem treeEq4706 : B4706.tree = HexagonCover.NBand.M8300_8500.SplitData.node4706 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4707
  · rfl

def B4705 : Block := .branch 167 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B4706, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4705 : B4705.tree = HexagonCover.NBand.M8300_8500.SplitData.node4705 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4706
  · rfl

def B4704 : Block := .branch 146 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B4705, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4704 : B4704.tree = HexagonCover.NBand.M8300_8500.SplitData.node4704 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4705
  · rfl
  · rfl

def B4703 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4704, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4703 : B4703.tree = HexagonCover.NBand.M8300_8500.SplitData.node4703 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4704
  · rfl
  · rfl
  · rfl

theorem accepted4703 : B4703.accepted = true := by decide +kernel
theorem checked4703 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4703 (maskNeeds ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496]) := by
  rw [← treeEq4703]
  exact B4703.sound accepted4703
#print axioms checked4703

def B4726 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq4726 : B4726.tree = HexagonCover.NBand.M8300_8500.SplitData.node4726 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4725 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4726, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq4725 : B4725.tree = HexagonCover.NBand.M8300_8500.SplitData.node4725 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4726
  · rfl
  · rfl

def B4724 : Block := .branch 166 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![B4725, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 638).pointIds 638), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq4724 : B4724.tree = HexagonCover.NBand.M8300_8500.SplitData.node4724 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4725
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4723 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B4724, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4723 : B4723.tree = HexagonCover.NBand.M8300_8500.SplitData.node4723 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4724
  · rfl
  · rfl

def B4722 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4723, (.leaf 0 [] 0)]
theorem treeEq4722 : B4722.tree = HexagonCover.NBand.M8300_8500.SplitData.node4722 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4723
  · rfl

def B4721 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4722, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4721 : B4721.tree = HexagonCover.NBand.M8300_8500.SplitData.node4721 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4722
  · rfl

def B4720 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B4721, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4720 : B4720.tree = HexagonCover.NBand.M8300_8500.SplitData.node4720 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4721
  · rfl
  · rfl

def B4719 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 577).pointIds 577), B4720, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq4719 : B4719.tree = HexagonCover.NBand.M8300_8500.SplitData.node4719 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4720
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4718 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B4719, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4718 : B4718.tree = HexagonCover.NBand.M8300_8500.SplitData.node4718 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4719
  · rfl
  · rfl
  · rfl
  · rfl

def B4717 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4718, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4717 : B4717.tree = HexagonCover.NBand.M8300_8500.SplitData.node4717 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4718
  · rfl
  · rfl
  · rfl

def B4716 : Block := .branch 135 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B4717]
theorem treeEq4716 : B4716.tree = HexagonCover.NBand.M8300_8500.SplitData.node4716 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4717

def B4715 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4716, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4715 : B4715.tree = HexagonCover.NBand.M8300_8500.SplitData.node4715 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4716
  · rfl

theorem accepted4715 : B4715.accepted = true := by decide +kernel
theorem checked4715 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4715 (maskNeeds ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582558969657516196503068611329993934897216]) := by
  rw [← treeEq4715]
  exact B4715.sound accepted4715
#print axioms checked4715

def Tip4650_4652 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4652 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064] checked4652
def B4684 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq4684 : B4684.tree = HexagonCover.NBand.M8300_8500.SplitData.node4684 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4683 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4684, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq4683 : B4683.tree = HexagonCover.NBand.M8300_8500.SplitData.node4683 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4684
  · rfl
  · rfl

def B4682 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B4683, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4682 : B4682.tree = HexagonCover.NBand.M8300_8500.SplitData.node4682 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4683
  · rfl
  · rfl

def B4681 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4682, (.leaf 0 [] 0)]
theorem treeEq4681 : B4681.tree = HexagonCover.NBand.M8300_8500.SplitData.node4681 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4682
  · rfl

def B4680 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4681, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4680 : B4680.tree = HexagonCover.NBand.M8300_8500.SplitData.node4680 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4681
  · rfl

def B4679 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B4680, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4679 : B4679.tree = HexagonCover.NBand.M8300_8500.SplitData.node4679 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4680
  · rfl
  · rfl

def B4678 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 577).pointIds 577), B4679, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq4678 : B4678.tree = HexagonCover.NBand.M8300_8500.SplitData.node4678 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4679
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4677 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B4678, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4677 : B4677.tree = HexagonCover.NBand.M8300_8500.SplitData.node4677 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4678
  · rfl
  · rfl
  · rfl
  · rfl

def B4676 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4677, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4676 : B4676.tree = HexagonCover.NBand.M8300_8500.SplitData.node4676 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4677
  · rfl
  · rfl
  · rfl

def B4675 : Block := .branch 135 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B4676]
theorem treeEq4675 : B4675.tree = HexagonCover.NBand.M8300_8500.SplitData.node4675 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4676

def B4674 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393796575557201053662835845606834635374608, 393248, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4675, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4674 : B4674.tree = HexagonCover.NBand.M8300_8500.SplitData.node4674 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4675
  · rfl

def B4651 : Block := .branch 121 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip4650_4652, (.leaf 5 (Common.fact 256).pointIds 256), B4674]
theorem treeEq4651 : B4651.tree = HexagonCover.NBand.M8300_8500.SplitData.node4651 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4674

def B4689 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4689 : B4689.tree = HexagonCover.NBand.M8300_8500.SplitData.node4689 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4688 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4689, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4688 : B4688.tree = HexagonCover.NBand.M8300_8500.SplitData.node4688 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4689
  · rfl

def B4687 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4688]
theorem treeEq4687 : B4687.tree = HexagonCover.NBand.M8300_8500.SplitData.node4687 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4688

def B4686 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4687, (.leaf 0 [] 0)]
theorem treeEq4686 : B4686.tree = HexagonCover.NBand.M8300_8500.SplitData.node4686 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4687
  · rfl

def B4685 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4686, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4685 : B4685.tree = HexagonCover.NBand.M8300_8500.SplitData.node4685 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4686
  · rfl

def B4650 : Block := .branch 119 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4651, B4685, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq4650 : B4650.tree = HexagonCover.NBand.M8300_8500.SplitData.node4650 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4651
  · exact treeEq4685
  · rfl
  · rfl

theorem accepted4650 : B4650.accepted = true := by decide +kernel
theorem checked4650 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4650 (maskNeeds ![576460752303423873, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4650]
  exact B4650.sound accepted4650
#print axioms checked4650

end HexagonCover.NBand.M8300_8500.SplitTree.Run0064
