import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0063
import HexagonCover.NBand.M8300_8500.SplitTree.Run0064
import HexagonCover.NBand.M8300_8500.SplitTree.Run0099
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0101
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0017_4114 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4114 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0063.checked4114
def Tip0017_0024 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0024 ![2251799813685633, 540432505040274946, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0064.checked0024
def Tip0017_4611 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4611 ![385, 146437906389534210, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0099.checked4611
def B4113 : Block := .branch 118 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), Tip0017_4114, (.leaf 4 (Common.fact 814).pointIds 814), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq4113 : B4113.tree = HexagonCover.NBand.M8300_8500.SplitData.node4113 := by
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

def B4112 : Block := .branch 128 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B4113, (.leaf 4 (Common.fact 813).pointIds 813), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq4112 : B4112.tree = HexagonCover.NBand.M8300_8500.SplitData.node4112 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4113
  · rfl
  · rfl
  · rfl

def B4111 : Block := .branch 120 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B4112, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq4111 : B4111.tree = HexagonCover.NBand.M8300_8500.SplitData.node4111 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4112
  · rfl
  · rfl

def B4110 : Block := .branch 143 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B4111]
theorem treeEq4110 : B4110.tree = HexagonCover.NBand.M8300_8500.SplitData.node4110 := by
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
  · exact treeEq4111

def B4109 : Block := .branch 140 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B4110, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq4109 : B4109.tree = HexagonCover.NBand.M8300_8500.SplitData.node4109 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4110
  · rfl
  · rfl

def B4108 : Block := .branch 148 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B4109, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq4108 : B4108.tree = HexagonCover.NBand.M8300_8500.SplitData.node4108 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4109
  · rfl
  · rfl

def B4107 : Block := .branch 168 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 990).pointIds 990), (.leaf 2 (Common.fact 991).pointIds 991), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B4108]
theorem treeEq4107 : B4107.tree = HexagonCover.NBand.M8300_8500.SplitData.node4107 := by
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
  · exact treeEq4108

def B0023 : Block := .branch 55 ![2251799813685633, 504474076765488642, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 133).pointIds 133), Tip0017_0024, B4107, (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 137).pointIds 137)]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M8300_8500.SplitData.node0023 := by
  change Tree.branch (55 : Fin 177) _ = Tree.branch (55 : Fin 177) _
  apply congrArg (Tree.branch (55 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4107
  · rfl
  · rfl
  · rfl
  · rfl

def B0022 : Block := .branch 58 ![2251799813685633, 216243700613776898, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 127).pointIds 127), B0023, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M8300_8500.SplitData.node0022 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0023
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0021 : Block := .branch 56 ![2251799813685633, 144186106575848962, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 121).pointIds 121), B0022, (.leaf 2 (Common.fact 122).pointIds 122), (.leaf 3 (Common.fact 123).pointIds 123), (.leaf 4 (Common.fact 124).pointIds 124), (.leaf 5 (Common.fact 125).pointIds 125), (.leaf 6 (Common.fact 126).pointIds 126)]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M8300_8500.SplitData.node0021 := by
  change Tree.branch (56 : Fin 177) _ = Tree.branch (56 : Fin 177) _
  apply congrArg (Tree.branch (56 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0022
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0020 : Block := .branch 75 ![2251799813685633, 144186106575848962, 6148, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B0021, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), (.leaf 6 (Common.fact 120).pointIds 120)]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M8300_8500.SplitData.node0020 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0021
  · rfl
  · rfl
  · rfl
  · rfl

def B0019 : Block := .branch 147 ![2251799813685633, 144186106575848962, 6148, 81248480658378078202179321094152, 98320, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B0020, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 114).pointIds 114)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M8300_8500.SplitData.node0019 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl

def B0018 : Block := .branch 124 ![2251799813685633, 144186106575848962, 6148, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 103).pointIds 103), (.leaf 1 (Common.fact 104).pointIds 104), (.leaf 2 (Common.fact 105).pointIds 105), (.leaf 3 (Common.fact 106).pointIds 106), (.leaf 4 (Common.fact 107).pointIds 107), (.leaf 5 (Common.fact 108).pointIds 108), B0019]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M8300_8500.SplitData.node0018 := by
  change Tree.branch (124 : Fin 177) _ = Tree.branch (124 : Fin 177) _
  apply congrArg (Tree.branch (124 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019

def B0017 : Block := .branch 51 ![385, 144186106575848962, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![B0018, Tip0017_4611, (.leaf 2 (Common.fact 99).pointIds 99), (.leaf 3 (Common.fact 100).pointIds 100), (.leaf 4 (Common.fact 101).pointIds 101), (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 0 [] 0)]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M8300_8500.SplitData.node0017 := by
  change Tree.branch (51 : Fin 177) _ = Tree.branch (51 : Fin 177) _
  apply congrArg (Tree.branch (51 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0018
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0017 : B0017.accepted = true := by decide +kernel
theorem checked0017 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0017 (maskNeeds ![385, 144186106575848962, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq0017]
  exact B0017.sound accepted0017
#print axioms checked0017

def B7334 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7334 : B7334.tree = HexagonCover.NBand.M8300_8500.SplitData.node7334 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7333 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7334, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7333 : B7333.tree = HexagonCover.NBand.M8300_8500.SplitData.node7333 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7334
  · rfl
  · rfl

def B7332 : Block := .branch 173 ![604462909807314587353473, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7333]
theorem treeEq7332 : B7332.tree = HexagonCover.NBand.M8300_8500.SplitData.node7332 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7333

def B7336 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1473).pointIds 1473)]
theorem treeEq7336 : B7336.tree = HexagonCover.NBand.M8300_8500.SplitData.node7336 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7335 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7336, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1472).pointIds 1472)]
theorem treeEq7335 : B7335.tree = HexagonCover.NBand.M8300_8500.SplitData.node7335 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7336
  · rfl
  · rfl

def B7331 : Block := .branch 79 ![385, 144185556820035074, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7332, (.leaf 1 (Common.fact 1551).pointIds 1551), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B7335]
theorem treeEq7331 : B7331.tree = HexagonCover.NBand.M8300_8500.SplitData.node7331 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7332
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7335

def B7338 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1476).pointIds 1476)]
theorem treeEq7338 : B7338.tree = HexagonCover.NBand.M8300_8500.SplitData.node7338 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7337 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7338, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1474).pointIds 1474)]
theorem treeEq7337 : B7337.tree = HexagonCover.NBand.M8300_8500.SplitData.node7337 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7338
  · rfl
  · rfl

def B7330 : Block := .branch 77 ![385, 144185556820035074, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 163).pointIds 163), B7331, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7337]
theorem treeEq7330 : B7330.tree = HexagonCover.NBand.M8300_8500.SplitData.node7330 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7331
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7337

def B7340 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1478).pointIds 1478)]
theorem treeEq7340 : B7340.tree = HexagonCover.NBand.M8300_8500.SplitData.node7340 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7339 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7340, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1477).pointIds 1477)]
theorem treeEq7339 : B7339.tree = HexagonCover.NBand.M8300_8500.SplitData.node7339 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7340
  · rfl
  · rfl

def B7329 : Block := .branch 75 ![385, 144185556820035074, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B7330, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7339]
theorem treeEq7329 : B7329.tree = HexagonCover.NBand.M8300_8500.SplitData.node7329 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7330
  · rfl
  · rfl
  · rfl
  · exact treeEq7339

def B7342 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7342 : B7342.tree = HexagonCover.NBand.M8300_8500.SplitData.node7342 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7341 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7342, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1479).pointIds 1479)]
theorem treeEq7341 : B7341.tree = HexagonCover.NBand.M8300_8500.SplitData.node7341 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7342
  · rfl
  · rfl

def B7328 : Block := .branch 66 ![385, 144185556820035074, 23639520545407055697924, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 148).pointIds 148), B7329, (.leaf 2 (Common.fact 1553).pointIds 1553), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7341]
theorem treeEq7328 : B7328.tree = HexagonCover.NBand.M8300_8500.SplitData.node7328 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7329
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7341

theorem accepted7328 : B7328.accepted = true := by decide +kernel
theorem checked7328 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7328 (maskNeeds ![385, 144185556820035074, 23639520545407055697924, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7328]
  exact B7328.sound accepted7328
#print axioms checked7328

def Tip7327_7328 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7328 ![385, 144185556820035074, 23639520545407055697924, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7328
def B7353 : Block := .branch 129 ![385, 1538, 6148, 18889465931478580879368, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 1491).pointIds 1491), (.leaf 4 (Common.fact 1492).pointIds 1492), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1493).pointIds 1493)]
theorem treeEq7353 : B7353.tree = HexagonCover.NBand.M8300_8500.SplitData.node7353 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7352 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7353, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7352 : B7352.tree = HexagonCover.NBand.M8300_8500.SplitData.node7352 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7353
  · rfl
  · rfl

def B7351 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1541).pointIds 1541), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7352]
theorem treeEq7351 : B7351.tree = HexagonCover.NBand.M8300_8500.SplitData.node7351 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7352

def B7350 : Block := .branch 173 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7351, (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7350 : B7350.tree = HexagonCover.NBand.M8300_8500.SplitData.node7350 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7351
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7349 : Block := .branch 162 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7350]
theorem treeEq7349 : B7349.tree = HexagonCover.NBand.M8300_8500.SplitData.node7349 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7350

def B7348 : Block := .branch 165 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7349, (.leaf 0 [] 0)]
theorem treeEq7348 : B7348.tree = HexagonCover.NBand.M8300_8500.SplitData.node7348 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7349
  · rfl

def B7347 : Block := .branch 167 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7348, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7347 : B7347.tree = HexagonCover.NBand.M8300_8500.SplitData.node7347 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7348
  · rfl

def B7346 : Block := .branch 146 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7347, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7346 : B7346.tree = HexagonCover.NBand.M8300_8500.SplitData.node7346 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7347
  · rfl
  · rfl

def B7345 : Block := .branch 150 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7346, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7345 : B7345.tree = HexagonCover.NBand.M8300_8500.SplitData.node7345 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7346
  · rfl
  · rfl

def B7344 : Block := .branch 168 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7345, (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7344 : B7344.tree = HexagonCover.NBand.M8300_8500.SplitData.node7344 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7345
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7343 : Block := .branch 170 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7344]
theorem treeEq7343 : B7343.tree = HexagonCover.NBand.M8300_8500.SplitData.node7343 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7344

def B7327 : Block := .branch 74 ![590295810358705652097, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), Tip7327_7328, B7343, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7327 : B7327.tree = HexagonCover.NBand.M8300_8500.SplitData.node7327 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7343
  · rfl
  · rfl
  · rfl

theorem accepted7327 : B7327.accepted = true := by decide +kernel
theorem checked7327 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7327 (maskNeeds ![590295810358705652097, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7327]
  exact B7327.sound accepted7327
#print axioms checked7327

def Tip7324_7327 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7327 ![590295810358705652097, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7327
def B7364 : Block := .branch 118 ![385, 1538, 6148, 79228171958997303332834402312, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1494).pointIds 1494), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1495).pointIds 1495)]
theorem treeEq7364 : B7364.tree = HexagonCover.NBand.M8300_8500.SplitData.node7364 := by
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

def B7363 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7364, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7363 : B7363.tree = HexagonCover.NBand.M8300_8500.SplitData.node7363 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7364
  · rfl
  · rfl

def B7362 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1541).pointIds 1541), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7363]
theorem treeEq7362 : B7362.tree = HexagonCover.NBand.M8300_8500.SplitData.node7362 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7363

def B7361 : Block := .branch 173 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7362, (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7361 : B7361.tree = HexagonCover.NBand.M8300_8500.SplitData.node7361 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7362
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7360 : Block := .branch 162 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7361]
theorem treeEq7360 : B7360.tree = HexagonCover.NBand.M8300_8500.SplitData.node7360 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7361

def B7359 : Block := .branch 165 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7360, (.leaf 0 [] 0)]
theorem treeEq7359 : B7359.tree = HexagonCover.NBand.M8300_8500.SplitData.node7359 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7360
  · rfl

def B7358 : Block := .branch 167 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7359, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7358 : B7358.tree = HexagonCover.NBand.M8300_8500.SplitData.node7358 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7359
  · rfl

def B7357 : Block := .branch 146 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7358, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7357 : B7357.tree = HexagonCover.NBand.M8300_8500.SplitData.node7357 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7358
  · rfl
  · rfl

def B7356 : Block := .branch 150 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7357, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7356 : B7356.tree = HexagonCover.NBand.M8300_8500.SplitData.node7356 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7357
  · rfl
  · rfl

def B7355 : Block := .branch 168 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7356, (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7355 : B7355.tree = HexagonCover.NBand.M8300_8500.SplitData.node7355 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7356
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7354 : Block := .branch 170 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7355]
theorem treeEq7354 : B7354.tree = HexagonCover.NBand.M8300_8500.SplitData.node7354 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7355

def B7326 : Block := .branch 73 ![590295810358705652097, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), Tip7324_7327, B7354, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7326 : B7326.tree = HexagonCover.NBand.M8300_8500.SplitData.node7326 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7354
  · rfl
  · rfl
  · rfl

def B7366 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1497).pointIds 1497)]
theorem treeEq7366 : B7366.tree = HexagonCover.NBand.M8300_8500.SplitData.node7366 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7365 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7366, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1496).pointIds 1496)]
theorem treeEq7365 : B7365.tree = HexagonCover.NBand.M8300_8500.SplitData.node7365 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7366
  · rfl
  · rfl

def B7325 : Block := .branch 69 ![385, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7326, (.leaf 1 (Common.fact 1552).pointIds 1552), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B7365]
theorem treeEq7325 : B7325.tree = HexagonCover.NBand.M8300_8500.SplitData.node7325 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7326
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7365

def B7368 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1460).pointIds 1460)]
theorem treeEq7368 : B7368.tree = HexagonCover.NBand.M8300_8500.SplitData.node7368 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7367 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7368, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1498).pointIds 1498)]
theorem treeEq7367 : B7367.tree = HexagonCover.NBand.M8300_8500.SplitData.node7367 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7368
  · rfl
  · rfl

def B7324 : Block := .branch 67 ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 153).pointIds 153), B7325, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7367]
theorem treeEq7324 : B7324.tree = HexagonCover.NBand.M8300_8500.SplitData.node7324 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7325
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7367

theorem accepted7324 : B7324.accepted = true := by decide +kernel
theorem checked7324 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7324 (maskNeeds ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7324]
  exact B7324.sound accepted7324
#print axioms checked7324

def B7387 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7387 : B7387.tree = HexagonCover.NBand.M8300_8500.SplitData.node7387 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7386 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7387, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7386 : B7386.tree = HexagonCover.NBand.M8300_8500.SplitData.node7386 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7387
  · rfl
  · rfl

def B7385 : Block := .branch 173 ![604462909807314587353473, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7386]
theorem treeEq7385 : B7385.tree = HexagonCover.NBand.M8300_8500.SplitData.node7385 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7386

def B7389 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1473).pointIds 1473)]
theorem treeEq7389 : B7389.tree = HexagonCover.NBand.M8300_8500.SplitData.node7389 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7388 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7389, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1472).pointIds 1472)]
theorem treeEq7388 : B7388.tree = HexagonCover.NBand.M8300_8500.SplitData.node7388 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7389
  · rfl
  · rfl

def B7384 : Block := .branch 79 ![385, 144185556820035074, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7385, (.leaf 1 (Common.fact 1551).pointIds 1551), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B7388]
theorem treeEq7384 : B7384.tree = HexagonCover.NBand.M8300_8500.SplitData.node7384 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7385
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7388

def B7391 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1476).pointIds 1476)]
theorem treeEq7391 : B7391.tree = HexagonCover.NBand.M8300_8500.SplitData.node7391 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7390 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7391, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1474).pointIds 1474)]
theorem treeEq7390 : B7390.tree = HexagonCover.NBand.M8300_8500.SplitData.node7390 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7391
  · rfl
  · rfl

def B7383 : Block := .branch 77 ![385, 144185556820035074, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 163).pointIds 163), B7384, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7390]
theorem treeEq7383 : B7383.tree = HexagonCover.NBand.M8300_8500.SplitData.node7383 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7384
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7390

def B7393 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1478).pointIds 1478)]
theorem treeEq7393 : B7393.tree = HexagonCover.NBand.M8300_8500.SplitData.node7393 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7392 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7393, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1477).pointIds 1477)]
theorem treeEq7392 : B7392.tree = HexagonCover.NBand.M8300_8500.SplitData.node7392 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7393
  · rfl
  · rfl

def B7382 : Block := .branch 75 ![385, 144185556820035074, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B7383, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7392]
theorem treeEq7382 : B7382.tree = HexagonCover.NBand.M8300_8500.SplitData.node7382 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7383
  · rfl
  · rfl
  · rfl
  · exact treeEq7392

def B7395 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7395 : B7395.tree = HexagonCover.NBand.M8300_8500.SplitData.node7395 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7394 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7395, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1479).pointIds 1479)]
theorem treeEq7394 : B7394.tree = HexagonCover.NBand.M8300_8500.SplitData.node7394 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7395
  · rfl
  · rfl

def B7381 : Block := .branch 66 ![385, 144185556820035074, 23639556574204074661892, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 148).pointIds 148), B7382, (.leaf 2 (Common.fact 1556).pointIds 1556), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7394]
theorem treeEq7381 : B7381.tree = HexagonCover.NBand.M8300_8500.SplitData.node7381 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7382
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7394

theorem accepted7381 : B7381.accepted = true := by decide +kernel
theorem checked7381 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7381 (maskNeeds ![385, 144185556820035074, 23639556574204074661892, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7381]
  exact B7381.sound accepted7381
#print axioms checked7381

end HexagonCover.NBand.M8300_8500.SplitTree.Run0101
