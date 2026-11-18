import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0097
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0098
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip6357_6358 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6358 ![385, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] HexagonCover.NBand.M8300_8500.SplitTree.Run0097.checked6358
def B7085 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 11150372599265311570767859136324180753088528, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 937).pointIds 937), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1460).pointIds 1460)]
theorem treeEq7085 : B7085.tree = HexagonCover.NBand.M8300_8500.SplitData.node7085 := by
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

def B7084 : Block := .branch 143 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B7085, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1459).pointIds 1459)]
theorem treeEq7084 : B7084.tree = HexagonCover.NBand.M8300_8500.SplitData.node7084 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7085
  · rfl
  · rfl

def B7083 : Block := .branch 144 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B7084, (.leaf 6 (Common.fact 1458).pointIds 1458)]
theorem treeEq7083 : B7083.tree = HexagonCover.NBand.M8300_8500.SplitData.node7083 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7084
  · rfl

def B7082 : Block := .branch 147 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7083, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1457).pointIds 1457)]
theorem treeEq7082 : B7082.tree = HexagonCover.NBand.M8300_8500.SplitData.node7082 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7083
  · rfl
  · rfl

def B7081 : Block := .branch 148 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7082, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1456).pointIds 1456)]
theorem treeEq7081 : B7081.tree = HexagonCover.NBand.M8300_8500.SplitData.node7081 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7082
  · rfl
  · rfl

def B7080 : Block := .branch 149 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1365).pointIds 1365), (.leaf 1 (Common.fact 1366).pointIds 1366), (.leaf 2 (Common.fact 1367).pointIds 1367), (.leaf 3 (Common.fact 1368).pointIds 1368), B7081, (.leaf 5 (Common.fact 1369).pointIds 1369), (.leaf 6 (Common.fact 1455).pointIds 1455)]
theorem treeEq7080 : B7080.tree = HexagonCover.NBand.M8300_8500.SplitData.node7080 := by
  change Tree.branch (149 : Fin 177) _ = Tree.branch (149 : Fin 177) _
  apply congrArg (Tree.branch (149 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7081
  · rfl
  · rfl

def B7079 : Block := .branch 150 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7080, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1454).pointIds 1454)]
theorem treeEq7079 : B7079.tree = HexagonCover.NBand.M8300_8500.SplitData.node7079 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7080
  · rfl
  · rfl

def B7078 : Block := .branch 73 ![385, 1538, 6148, 332388247426887346304153944391180296, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), B7079, (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7078 : B7078.tree = HexagonCover.NBand.M8300_8500.SplitData.node7078 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7079
  · rfl
  · rfl
  · rfl
  · rfl

def B7077 : Block := .branch 118 ![385, 1538, 6148, 81248480658378078202179321094152, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B7078, (.leaf 4 (Common.fact 1360).pointIds 1360), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1453).pointIds 1453)]
theorem treeEq7077 : B7077.tree = HexagonCover.NBand.M8300_8500.SplitData.node7077 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7078
  · rfl
  · rfl
  · rfl

def B7076 : Block := .branch 128 ![385, 1538, 6148, 81248480658378078202179321094152, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B7077, (.leaf 4 (Common.fact 1358).pointIds 1358), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1452).pointIds 1452)]
theorem treeEq7076 : B7076.tree = HexagonCover.NBand.M8300_8500.SplitData.node7076 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7077
  · rfl
  · rfl
  · rfl

def B7075 : Block := .branch 151 ![385, 1538, 6148, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7076, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1451).pointIds 1451)]
theorem treeEq7075 : B7075.tree = HexagonCover.NBand.M8300_8500.SplitData.node7075 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7076
  · rfl
  · rfl

def B7074 : Block := .branch 168 ![385, 146437906389534210, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325295164057013718614080] ![B7075, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1450).pointIds 1450)]
theorem treeEq7074 : B7074.tree = HexagonCover.NBand.M8300_8500.SplitData.node7074 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7075
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6357 : Block := .branch 67 ![385, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 153).pointIds 153), Tip6357_6358, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7074]
theorem treeEq6357 : B6357.tree = HexagonCover.NBand.M8300_8500.SplitData.node6357 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7074

theorem accepted6357 : B6357.accepted = true := by decide +kernel
theorem checked6357 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6357 (maskNeeds ![385, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq6357]
  exact B6357.sound accepted6357
#print axioms checked6357

def B7106 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7106 : B7106.tree = HexagonCover.NBand.M8300_8500.SplitData.node7106 := by
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

def B7105 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7106, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7105 : B7105.tree = HexagonCover.NBand.M8300_8500.SplitData.node7105 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7106
  · rfl
  · rfl

def B7104 : Block := .branch 173 ![604462909807314587353473, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1464).pointIds 1464), (.leaf 2 (Common.fact 1465).pointIds 1465), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B7105]
theorem treeEq7104 : B7104.tree = HexagonCover.NBand.M8300_8500.SplitData.node7104 := by
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
  · exact treeEq7105

def B7108 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1473).pointIds 1473)]
theorem treeEq7108 : B7108.tree = HexagonCover.NBand.M8300_8500.SplitData.node7108 := by
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

def B7107 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7108, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1472).pointIds 1472)]
theorem treeEq7107 : B7107.tree = HexagonCover.NBand.M8300_8500.SplitData.node7107 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7108
  · rfl
  · rfl

def B7103 : Block := .branch 79 ![385, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7104, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B7107]
theorem treeEq7103 : B7103.tree = HexagonCover.NBand.M8300_8500.SplitData.node7103 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7104
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7107

def B7110 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1476).pointIds 1476)]
theorem treeEq7110 : B7110.tree = HexagonCover.NBand.M8300_8500.SplitData.node7110 := by
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

def B7109 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7110, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1474).pointIds 1474)]
theorem treeEq7109 : B7109.tree = HexagonCover.NBand.M8300_8500.SplitData.node7109 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7110
  · rfl
  · rfl

def B7102 : Block := .branch 77 ![385, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 163).pointIds 163), B7103, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7109]
theorem treeEq7102 : B7102.tree = HexagonCover.NBand.M8300_8500.SplitData.node7102 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7103
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7109

def B7112 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1478).pointIds 1478)]
theorem treeEq7112 : B7112.tree = HexagonCover.NBand.M8300_8500.SplitData.node7112 := by
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

def B7111 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7112, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1477).pointIds 1477)]
theorem treeEq7111 : B7111.tree = HexagonCover.NBand.M8300_8500.SplitData.node7111 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7112
  · rfl
  · rfl

def B7101 : Block := .branch 75 ![385, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B7102, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7111]
theorem treeEq7101 : B7101.tree = HexagonCover.NBand.M8300_8500.SplitData.node7101 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7102
  · rfl
  · rfl
  · rfl
  · exact treeEq7111

def B7114 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7114 : B7114.tree = HexagonCover.NBand.M8300_8500.SplitData.node7114 := by
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

def B7113 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7114, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1479).pointIds 1479)]
theorem treeEq7113 : B7113.tree = HexagonCover.NBand.M8300_8500.SplitData.node7113 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7114
  · rfl
  · rfl

def B7100 : Block := .branch 66 ![385, 146437906389534210, 23630315187218954590212, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 148).pointIds 148), B7101, (.leaf 2 (Common.fact 1471).pointIds 1471), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7113]
theorem treeEq7100 : B7100.tree = HexagonCover.NBand.M8300_8500.SplitData.node7100 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7101
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7113

theorem accepted7100 : B7100.accepted = true := by decide +kernel
theorem checked7100 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7100 (maskNeeds ![385, 146437906389534210, 23630315187218954590212, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7100]
  exact B7100.sound accepted7100
#print axioms checked7100

def Tip7099_7100 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7100 ![385, 146437906389534210, 23630315187218954590212, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7100
def B7125 : Block := .branch 129 ![385, 1538, 6148, 18889465931478580879368, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 1491).pointIds 1491), (.leaf 4 (Common.fact 1492).pointIds 1492), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1493).pointIds 1493)]
theorem treeEq7125 : B7125.tree = HexagonCover.NBand.M8300_8500.SplitData.node7125 := by
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

def B7124 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7125, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7124 : B7124.tree = HexagonCover.NBand.M8300_8500.SplitData.node7124 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7125
  · rfl
  · rfl

def B7123 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 267608942382367477698428619271780338071863312, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1487).pointIds 1487), (.leaf 2 (Common.fact 1488).pointIds 1488), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1332).pointIds 1332), (.leaf 5 (Common.fact 1239).pointIds 1239), B7124]
theorem treeEq7123 : B7123.tree = HexagonCover.NBand.M8300_8500.SplitData.node7123 := by
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
  · exact treeEq7124

def B7122 : Block := .branch 173 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 267608942382367477698428619271780338071863312, 393248, 7307508208437902985941625488729005202703704916032] ![B7123, (.leaf 1 (Common.fact 1464).pointIds 1464), (.leaf 2 (Common.fact 1465).pointIds 1465), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7122 : B7122.tree = HexagonCover.NBand.M8300_8500.SplitData.node7122 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7123
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7121 : Block := .branch 162 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 1694856635088327358756714588721275474454609936, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7122]
theorem treeEq7121 : B7121.tree = HexagonCover.NBand.M8300_8500.SplitData.node7121 := by
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
  · exact treeEq7122

def B7120 : Block := .branch 165 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 1694856635088327358756714588721275474454609936, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7121, (.leaf 0 [] 0)]
theorem treeEq7120 : B7120.tree = HexagonCover.NBand.M8300_8500.SplitData.node7120 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7121
  · rfl

def B7119 : Block := .branch 167 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 1694856635088327358756714588721275474454609936, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7120, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7119 : B7119.tree = HexagonCover.NBand.M8300_8500.SplitData.node7119 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7120
  · rfl

def B7118 : Block := .branch 146 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 1605653654294204866190571715630682028430688272, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7119, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7118 : B7118.tree = HexagonCover.NBand.M8300_8500.SplitData.node7118 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7119
  · rfl
  · rfl

def B7117 : Block := .branch 150 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7118, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7117 : B7117.tree = HexagonCover.NBand.M8300_8500.SplitData.node7117 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7118
  · rfl
  · rfl

def B7116 : Block := .branch 168 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![B7117, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7116 : B7116.tree = HexagonCover.NBand.M8300_8500.SplitData.node7116 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7117
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7115 : Block := .branch 170 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228181403730269072124829704, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7116]
theorem treeEq7115 : B7115.tree = HexagonCover.NBand.M8300_8500.SplitData.node7115 := by
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
  · exact treeEq7116

def B7099 : Block := .branch 74 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), Tip7099_7100, B7115, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7099 : B7099.tree = HexagonCover.NBand.M8300_8500.SplitData.node7099 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7115
  · rfl
  · rfl
  · rfl

theorem accepted7099 : B7099.accepted = true := by decide +kernel
theorem checked7099 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7099 (maskNeeds ![590295810358705652097, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7099]
  exact B7099.sound accepted7099
#print axioms checked7099

def Tip7096_7099 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7099 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7099
def B7136 : Block := .branch 118 ![385, 1538, 6148, 79228171958997303332834402312, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1494).pointIds 1494), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1495).pointIds 1495)]
theorem treeEq7136 : B7136.tree = HexagonCover.NBand.M8300_8500.SplitData.node7136 := by
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

def B7135 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7136, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7135 : B7135.tree = HexagonCover.NBand.M8300_8500.SplitData.node7135 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7136
  · rfl
  · rfl

def B7134 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 267608942382367477698428619271780338071863312, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1487).pointIds 1487), (.leaf 2 (Common.fact 1488).pointIds 1488), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1332).pointIds 1332), (.leaf 5 (Common.fact 1239).pointIds 1239), B7135]
theorem treeEq7134 : B7134.tree = HexagonCover.NBand.M8300_8500.SplitData.node7134 := by
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
  · exact treeEq7135

def B7133 : Block := .branch 173 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 267608942382367477698428619271780338071863312, 393248, 7307508208437902985941625488729005202703704916032] ![B7134, (.leaf 1 (Common.fact 1464).pointIds 1464), (.leaf 2 (Common.fact 1465).pointIds 1465), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7133 : B7133.tree = HexagonCover.NBand.M8300_8500.SplitData.node7133 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7134
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7132 : Block := .branch 162 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 1694856635088327358756714588721275474454609936, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7133]
theorem treeEq7132 : B7132.tree = HexagonCover.NBand.M8300_8500.SplitData.node7132 := by
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
  · exact treeEq7133

def B7131 : Block := .branch 165 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 1694856635088327358756714588721275474454609936, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7132, (.leaf 0 [] 0)]
theorem treeEq7131 : B7131.tree = HexagonCover.NBand.M8300_8500.SplitData.node7131 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7132
  · rfl

def B7130 : Block := .branch 167 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 1694856635088327358756714588721275474454609936, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7131, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7130 : B7130.tree = HexagonCover.NBand.M8300_8500.SplitData.node7130 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7131
  · rfl

def B7129 : Block := .branch 146 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 1605653654294204866190571715630682028430688272, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7130, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7129 : B7129.tree = HexagonCover.NBand.M8300_8500.SplitData.node7129 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7130
  · rfl
  · rfl

def B7128 : Block := .branch 150 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7129, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7128 : B7128.tree = HexagonCover.NBand.M8300_8500.SplitData.node7128 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7129
  · rfl
  · rfl

def B7127 : Block := .branch 168 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![B7128, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7127 : B7127.tree = HexagonCover.NBand.M8300_8500.SplitData.node7127 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7126 : Block := .branch 170 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 79228171958997303332834402312, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7127]
theorem treeEq7126 : B7126.tree = HexagonCover.NBand.M8300_8500.SplitData.node7126 := by
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
  · exact treeEq7127

def B7098 : Block := .branch 73 ![590295810358705652097, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), Tip7096_7099, B7126, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7098 : B7098.tree = HexagonCover.NBand.M8300_8500.SplitData.node7098 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7126
  · rfl
  · rfl
  · rfl

def B7138 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1497).pointIds 1497)]
theorem treeEq7138 : B7138.tree = HexagonCover.NBand.M8300_8500.SplitData.node7138 := by
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

def B7137 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7138, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1496).pointIds 1496)]
theorem treeEq7137 : B7137.tree = HexagonCover.NBand.M8300_8500.SplitData.node7137 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7138
  · rfl
  · rfl

def B7097 : Block := .branch 69 ![385, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7098, (.leaf 1 (Common.fact 158).pointIds 158), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B7137]
theorem treeEq7097 : B7097.tree = HexagonCover.NBand.M8300_8500.SplitData.node7097 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7098
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7137

def B7140 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1460).pointIds 1460)]
theorem treeEq7140 : B7140.tree = HexagonCover.NBand.M8300_8500.SplitData.node7140 := by
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

def B7139 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7140, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1498).pointIds 1498)]
theorem treeEq7139 : B7139.tree = HexagonCover.NBand.M8300_8500.SplitData.node7139 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7140
  · rfl
  · rfl

def B7096 : Block := .branch 67 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 153).pointIds 153), B7097, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7139]
theorem treeEq7096 : B7096.tree = HexagonCover.NBand.M8300_8500.SplitData.node7096 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7097
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7139

theorem accepted7096 : B7096.accepted = true := by decide +kernel
theorem checked7096 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7096 (maskNeeds ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7096]
  exact B7096.sound accepted7096
#print axioms checked7096

def Tip7088_7096 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7096 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7096
def B7091 : Block := .branch 79 ![288230376151712129, 144115737831671298, 6148, 24584, 98320, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1466).pointIds 1466)]
theorem treeEq7091 : B7091.tree = HexagonCover.NBand.M8300_8500.SplitData.node7091 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7090 : Block := .branch 173 ![288230376151712129, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1463).pointIds 1463), (.leaf 1 (Common.fact 1464).pointIds 1464), (.leaf 2 (Common.fact 1465).pointIds 1465), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B7091]
theorem treeEq7090 : B7090.tree = HexagonCover.NBand.M8300_8500.SplitData.node7090 := by
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
  · exact treeEq7091

def B7095 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7095 : B7095.tree = HexagonCover.NBand.M8300_8500.SplitData.node7095 := by
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

def B7094 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7095, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7094 : B7094.tree = HexagonCover.NBand.M8300_8500.SplitData.node7094 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7095
  · rfl
  · rfl

def B7093 : Block := .branch 173 ![576460752303423873, 146437906389534210, 4740849255740373735428, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1467).pointIds 1467), (.leaf 1 (Common.fact 1464).pointIds 1464), (.leaf 2 (Common.fact 1465).pointIds 1465), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B7094]
theorem treeEq7093 : B7093.tree = HexagonCover.NBand.M8300_8500.SplitData.node7093 := by
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
  · exact treeEq7094

def B7092 : Block := .branch 59 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7093, Tip7088_7096, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7092 : B7092.tree = HexagonCover.NBand.M8300_8500.SplitData.node7092 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7093
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7089 : Block := .branch 58 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7090, B7092, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq7089 : B7089.tree = HexagonCover.NBand.M8300_8500.SplitData.node7089 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7090
  · exact treeEq7092
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7152 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1498039178285958879553700154897116617114712060461120] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1506).pointIds 1506)]
theorem treeEq7152 : B7152.tree = HexagonCover.NBand.M8300_8500.SplitData.node7152 := by
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

def B7151 : Block := .branch 174 ![385, 146437906389534210, 4740849255740373735428, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154897116617114712060461120] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1469).pointIds 1469), (.leaf 2 (Common.fact 1470).pointIds 1470), (.leaf 3 (Common.fact 1353).pointIds 1353), B7152, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1505).pointIds 1505)]
theorem treeEq7151 : B7151.tree = HexagonCover.NBand.M8300_8500.SplitData.node7151 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7152
  · rfl
  · rfl

def B7150 : Block := .branch 75 ![385, 146437906389534210, 4740921313334411663364, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), (.leaf 2 (Common.fact 1504).pointIds 1504), (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7151]
theorem treeEq7150 : B7150.tree = HexagonCover.NBand.M8300_8500.SplitData.node7150 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7151

def B7149 : Block := .branch 82 ![385, 146437906389534210, 4740921313334411663364, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), (.leaf 2 (Common.fact 1503).pointIds 1503), B7150, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq7149 : B7149.tree = HexagonCover.NBand.M8300_8500.SplitData.node7149 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7150
  · rfl
  · rfl
  · rfl

def B7148 : Block := .branch 83 ![385, 146437906389534210, 4740921313334411663364, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), (.leaf 2 (Common.fact 1502).pointIds 1502), B7149, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq7148 : B7148.tree = HexagonCover.NBand.M8300_8500.SplitData.node7148 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7149
  · rfl
  · rfl
  · rfl

def B7147 : Block := .branch 84 ![385, 146437906389534210, 4740921313334411663364, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 1501).pointIds 1501), B7148, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq7147 : B7147.tree = HexagonCover.NBand.M8300_8500.SplitData.node7147 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7148
  · rfl
  · rfl
  · rfl

def B7146 : Block := .branch 161 ![385, 146437906389534210, 4740921313334411663364, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1500).pointIds 1500), (.leaf 3 (Common.fact 820).pointIds 820), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7147]
theorem treeEq7146 : B7146.tree = HexagonCover.NBand.M8300_8500.SplitData.node7146 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7147

def B7145 : Block := .branch 150 ![385, 146437906389534210, 4740921313334411663364, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7146, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7145 : B7145.tree = HexagonCover.NBand.M8300_8500.SplitData.node7145 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7146
  · rfl
  · rfl

def B7144 : Block := .branch 59 ![374144419156711147060143317175368453031918731002241, 146437906389534210, 4740921313334411663364, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 1018).pointIds 1018), B7145, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7144 : B7144.tree = HexagonCover.NBand.M8300_8500.SplitData.node7144 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7145
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7143 : Block := .branch 168 ![385, 146437906389534210, 4740921313334411663364, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![B7144, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7143 : B7143.tree = HexagonCover.NBand.M8300_8500.SplitData.node7143 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7144
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7142 : Block := .branch 170 ![385, 146437906389534210, 4740921313334411663364, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7143]
theorem treeEq7142 : B7142.tree = HexagonCover.NBand.M8300_8500.SplitData.node7142 := by
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
  · exact treeEq7143

def B7141 : Block := .branch 85 ![385, 146437906389534210, 4740921313334411663364, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 1499).pointIds 1499), B7142, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7141 : B7141.tree = HexagonCover.NBand.M8300_8500.SplitData.node7141 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7142
  · rfl
  · rfl
  · rfl

def B7088 : Block := .branch 56 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 121).pointIds 121), B7089, B7141, (.leaf 3 (Common.fact 123).pointIds 123), (.leaf 4 (Common.fact 124).pointIds 124), (.leaf 5 (Common.fact 125).pointIds 125), (.leaf 6 (Common.fact 126).pointIds 126)]
theorem treeEq7088 : B7088.tree = HexagonCover.NBand.M8300_8500.SplitData.node7088 := by
  change Tree.branch (56 : Fin 177) _ = Tree.branch (56 : Fin 177) _
  apply congrArg (Tree.branch (56 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7089
  · exact treeEq7141
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted7088 : B7088.accepted = true := by decide +kernel
theorem checked7088 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7088 (maskNeeds ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7088]
  exact B7088.sound accepted7088
#print axioms checked7088

end HexagonCover.NBand.M8300_8500.SplitTree.Run0098
