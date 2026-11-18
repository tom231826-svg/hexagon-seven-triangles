import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0101
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0102
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip7380_7381 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7381 ![385, 144185556820035074, 23639556574204074661892, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0101.checked7381
def B7406 : Block := .branch 129 ![385, 1538, 6148, 18889465931478580879368, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 1491).pointIds 1491), (.leaf 4 (Common.fact 1492).pointIds 1492), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1493).pointIds 1493)]
theorem treeEq7406 : B7406.tree = HexagonCover.NBand.M8300_8500.SplitData.node7406 := by
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

def B7405 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7406, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7405 : B7405.tree = HexagonCover.NBand.M8300_8500.SplitData.node7405 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7406
  · rfl
  · rfl

def B7404 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1541).pointIds 1541), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7405]
theorem treeEq7404 : B7404.tree = HexagonCover.NBand.M8300_8500.SplitData.node7404 := by
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
  · exact treeEq7405

def B7403 : Block := .branch 173 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7404, (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7403 : B7403.tree = HexagonCover.NBand.M8300_8500.SplitData.node7403 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7404
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7402 : Block := .branch 162 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7403]
theorem treeEq7402 : B7402.tree = HexagonCover.NBand.M8300_8500.SplitData.node7402 := by
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
  · exact treeEq7403

def B7401 : Block := .branch 165 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7402, (.leaf 0 [] 0)]
theorem treeEq7401 : B7401.tree = HexagonCover.NBand.M8300_8500.SplitData.node7401 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7402
  · rfl

def B7400 : Block := .branch 167 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7401, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7400 : B7400.tree = HexagonCover.NBand.M8300_8500.SplitData.node7400 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7401
  · rfl

def B7399 : Block := .branch 146 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7400, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7399 : B7399.tree = HexagonCover.NBand.M8300_8500.SplitData.node7399 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7400
  · rfl
  · rfl

def B7398 : Block := .branch 150 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7399, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7398 : B7398.tree = HexagonCover.NBand.M8300_8500.SplitData.node7398 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7399
  · rfl
  · rfl

def B7397 : Block := .branch 168 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7398, (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7397 : B7397.tree = HexagonCover.NBand.M8300_8500.SplitData.node7397 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7398
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7396 : Block := .branch 170 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7397]
theorem treeEq7396 : B7396.tree = HexagonCover.NBand.M8300_8500.SplitData.node7396 := by
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
  · exact treeEq7397

def B7380 : Block := .branch 74 ![590295810358705652097, 144185556820035074, 4750090642725493807108, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), Tip7380_7381, B7396, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7380 : B7380.tree = HexagonCover.NBand.M8300_8500.SplitData.node7380 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7396
  · rfl
  · rfl
  · rfl

theorem accepted7380 : B7380.accepted = true := by decide +kernel
theorem checked7380 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7380 (maskNeeds ![590295810358705652097, 144185556820035074, 4750090642725493807108, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7380]
  exact B7380.sound accepted7380
#print axioms checked7380

def Tip7377_7380 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7380 ![590295810358705652097, 144185556820035074, 4750090642725493807108, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7380
def B7417 : Block := .branch 118 ![385, 1538, 6148, 79228171958997303332834402312, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1494).pointIds 1494), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1495).pointIds 1495)]
theorem treeEq7417 : B7417.tree = HexagonCover.NBand.M8300_8500.SplitData.node7417 := by
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

def B7416 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7417, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7416 : B7416.tree = HexagonCover.NBand.M8300_8500.SplitData.node7416 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7417
  · rfl
  · rfl

def B7415 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1541).pointIds 1541), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7416]
theorem treeEq7415 : B7415.tree = HexagonCover.NBand.M8300_8500.SplitData.node7415 := by
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
  · exact treeEq7416

def B7414 : Block := .branch 173 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7415, (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7414 : B7414.tree = HexagonCover.NBand.M8300_8500.SplitData.node7414 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7415
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7413 : Block := .branch 162 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7414]
theorem treeEq7413 : B7413.tree = HexagonCover.NBand.M8300_8500.SplitData.node7413 := by
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
  · exact treeEq7414

def B7412 : Block := .branch 165 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7413, (.leaf 0 [] 0)]
theorem treeEq7412 : B7412.tree = HexagonCover.NBand.M8300_8500.SplitData.node7412 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7413
  · rfl

def B7411 : Block := .branch 167 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7412, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7411 : B7411.tree = HexagonCover.NBand.M8300_8500.SplitData.node7411 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7412
  · rfl

def B7410 : Block := .branch 146 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7411, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7410 : B7410.tree = HexagonCover.NBand.M8300_8500.SplitData.node7410 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7411
  · rfl
  · rfl

def B7409 : Block := .branch 150 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7410, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7409 : B7409.tree = HexagonCover.NBand.M8300_8500.SplitData.node7409 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7410
  · rfl
  · rfl

def B7408 : Block := .branch 168 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7409, (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7408 : B7408.tree = HexagonCover.NBand.M8300_8500.SplitData.node7408 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7409
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7407 : Block := .branch 170 ![590295810358705652097, 144185556820035074, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7408]
theorem treeEq7407 : B7407.tree = HexagonCover.NBand.M8300_8500.SplitData.node7407 := by
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
  · exact treeEq7408

def B7379 : Block := .branch 73 ![590295810358705652097, 144185556820035074, 4750090642725493807108, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), Tip7377_7380, B7407, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7379 : B7379.tree = HexagonCover.NBand.M8300_8500.SplitData.node7379 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7407
  · rfl
  · rfl
  · rfl

def B7419 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1497).pointIds 1497)]
theorem treeEq7419 : B7419.tree = HexagonCover.NBand.M8300_8500.SplitData.node7419 := by
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

def B7418 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7419, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1496).pointIds 1496)]
theorem treeEq7418 : B7418.tree = HexagonCover.NBand.M8300_8500.SplitData.node7418 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7419
  · rfl
  · rfl

def B7378 : Block := .branch 69 ![385, 144185556820035074, 4750090642725493807108, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7379, (.leaf 1 (Common.fact 1552).pointIds 1552), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B7418]
theorem treeEq7378 : B7378.tree = HexagonCover.NBand.M8300_8500.SplitData.node7378 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7379
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7418

def B7421 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1460).pointIds 1460)]
theorem treeEq7421 : B7421.tree = HexagonCover.NBand.M8300_8500.SplitData.node7421 := by
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

def B7420 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7421, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1498).pointIds 1498)]
theorem treeEq7420 : B7420.tree = HexagonCover.NBand.M8300_8500.SplitData.node7420 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7421
  · rfl
  · rfl

def B7377 : Block := .branch 67 ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 153).pointIds 153), B7378, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7420]
theorem treeEq7377 : B7377.tree = HexagonCover.NBand.M8300_8500.SplitData.node7377 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7378
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7420

theorem accepted7377 : B7377.accepted = true := by decide +kernel
theorem checked7377 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7377 (maskNeeds ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7377]
  exact B7377.sound accepted7377
#print axioms checked7377

def Tip7369_7377 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7377 ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7377
def B7372 : Block := .branch 79 ![288230376151712129, 144185556820035074, 6148, 24584, 98320, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 1551).pointIds 1551), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1466).pointIds 1466)]
theorem treeEq7372 : B7372.tree = HexagonCover.NBand.M8300_8500.SplitData.node7372 := by
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

def B7371 : Block := .branch 173 ![288230376151712129, 144185556820035074, 4731607869854765291524, 79228162514264337593543974920, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1463).pointIds 1463), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7372]
theorem treeEq7371 : B7371.tree = HexagonCover.NBand.M8300_8500.SplitData.node7371 := by
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
  · exact treeEq7372

def B7376 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7376 : B7376.tree = HexagonCover.NBand.M8300_8500.SplitData.node7376 := by
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

def B7375 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7376, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7375 : B7375.tree = HexagonCover.NBand.M8300_8500.SplitData.node7375 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7376
  · rfl
  · rfl

def B7374 : Block := .branch 173 ![576460752303423873, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1467).pointIds 1467), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7375]
theorem treeEq7374 : B7374.tree = HexagonCover.NBand.M8300_8500.SplitData.node7374 := by
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
  · exact treeEq7375

def B7373 : Block := .branch 59 ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7374, Tip7369_7377, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7373 : B7373.tree = HexagonCover.NBand.M8300_8500.SplitData.node7373 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7374
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7370 : Block := .branch 58 ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7371, B7373, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq7370 : B7370.tree = HexagonCover.NBand.M8300_8500.SplitData.node7370 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7371
  · exact treeEq7373
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7433 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1498039178285958879553700154897116617114712060461120] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1506).pointIds 1506)]
theorem treeEq7433 : B7433.tree = HexagonCover.NBand.M8300_8500.SplitData.node7433 := by
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

def B7432 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154897116617114712060461120] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7433, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1505).pointIds 1505)]
theorem treeEq7432 : B7432.tree = HexagonCover.NBand.M8300_8500.SplitData.node7432 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7433
  · rfl
  · rfl

def B7431 : Block := .branch 75 ![385, 144115188075857410, 4750126671522512771076, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), (.leaf 2 (Common.fact 1562).pointIds 1562), (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7432]
theorem treeEq7431 : B7431.tree = HexagonCover.NBand.M8300_8500.SplitData.node7431 := by
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
  · exact treeEq7432

def B7430 : Block := .branch 82 ![385, 144115188075857410, 4750126671522512771076, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), (.leaf 2 (Common.fact 1561).pointIds 1561), B7431, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq7430 : B7430.tree = HexagonCover.NBand.M8300_8500.SplitData.node7430 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7431
  · rfl
  · rfl
  · rfl

def B7429 : Block := .branch 83 ![385, 144115188075857410, 4750126671522512771076, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), (.leaf 2 (Common.fact 1560).pointIds 1560), B7430, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq7429 : B7429.tree = HexagonCover.NBand.M8300_8500.SplitData.node7429 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7430
  · rfl
  · rfl
  · rfl

def B7428 : Block := .branch 84 ![385, 144115188075857410, 4750126671522512771076, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 1559).pointIds 1559), B7429, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq7428 : B7428.tree = HexagonCover.NBand.M8300_8500.SplitData.node7428 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7429
  · rfl
  · rfl
  · rfl

def B7427 : Block := .branch 161 ![385, 144115188075857410, 4750126671522512771076, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1558).pointIds 1558), (.leaf 3 (Common.fact 820).pointIds 820), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7428]
theorem treeEq7427 : B7427.tree = HexagonCover.NBand.M8300_8500.SplitData.node7427 := by
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
  · exact treeEq7428

def B7426 : Block := .branch 150 ![385, 144115188075857410, 4750126671522512771076, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7427, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7426 : B7426.tree = HexagonCover.NBand.M8300_8500.SplitData.node7426 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7427
  · rfl
  · rfl

def B7425 : Block := .branch 59 ![374144419156711147060143317175368453031918731002241, 144115188075857410, 4750126671522512771076, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 1018).pointIds 1018), B7426, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7425 : B7425.tree = HexagonCover.NBand.M8300_8500.SplitData.node7425 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7426
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7424 : Block := .branch 168 ![385, 144115188075857410, 4750126671522512771076, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![B7425, (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7424 : B7424.tree = HexagonCover.NBand.M8300_8500.SplitData.node7424 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7425
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7423 : Block := .branch 170 ![385, 144115188075857410, 4750126671522512771076, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7424]
theorem treeEq7423 : B7423.tree = HexagonCover.NBand.M8300_8500.SplitData.node7423 := by
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
  · exact treeEq7424

def B7422 : Block := .branch 85 ![385, 144115188075857410, 4750126671522512771076, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 1557).pointIds 1557), B7423, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7422 : B7422.tree = HexagonCover.NBand.M8300_8500.SplitData.node7422 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7423
  · rfl
  · rfl
  · rfl

def B7369 : Block := .branch 56 ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 121).pointIds 121), B7370, B7422, (.leaf 3 (Common.fact 123).pointIds 123), (.leaf 4 (Common.fact 124).pointIds 124), (.leaf 5 (Common.fact 125).pointIds 125), (.leaf 6 (Common.fact 126).pointIds 126)]
theorem treeEq7369 : B7369.tree = HexagonCover.NBand.M8300_8500.SplitData.node7369 := by
  change Tree.branch (56 : Fin 177) _ = Tree.branch (56 : Fin 177) _
  apply congrArg (Tree.branch (56 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7370
  · exact treeEq7422
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted7369 : B7369.accepted = true := by decide +kernel
theorem checked7369 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7369 (maskNeeds ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7369]
  exact B7369.sound accepted7369
#print axioms checked7369

def B7313 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 1223).pointIds 1223)]
theorem treeEq7313 : B7313.tree = HexagonCover.NBand.M8300_8500.SplitData.node7313 := by
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
  · rfl

def B7312 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38913942595572621100091312355903751681359409644568640] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7313, (.leaf 6 (Common.fact 1527).pointIds 1527)]
theorem treeEq7312 : B7312.tree = HexagonCover.NBand.M8300_8500.SplitData.node7312 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7313
  · rfl

def B7311 : Block := .branch 161 ![385, 144115188075857410, 135404441851452396041934852, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1546).pointIds 1546), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7312]
theorem treeEq7311 : B7311.tree = HexagonCover.NBand.M8300_8500.SplitData.node7311 := by
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
  · exact treeEq7312

def B7310 : Block := .branch 84 ![385, 144115188075857410, 116061628737618329246636036, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B7311, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq7310 : B7310.tree = HexagonCover.NBand.M8300_8500.SplitData.node7310 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7311
  · rfl
  · rfl
  · rfl
  · rfl

def B7309 : Block := .branch 85 ![385, 144115188075857410, 77376002509950195656038404, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B7310, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7309 : B7309.tree = HexagonCover.NBand.M8300_8500.SplitData.node7309 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7310
  · rfl
  · rfl
  · rfl
  · rfl

def B7308 : Block := .branch 66 ![385, 144115188075857410, 77376002509950195656038404, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 148).pointIds 148), B7309, (.leaf 2 (Common.fact 1545).pointIds 1545), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1523).pointIds 1523)]
theorem treeEq7308 : B7308.tree = HexagonCover.NBand.M8300_8500.SplitData.node7308 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7309
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7307 : Block := .branch 86 ![385, 144115188075857410, 4750054613928474843140, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B7308, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1346).pointIds 1346)]
theorem treeEq7307 : B7307.tree = HexagonCover.NBand.M8300_8500.SplitData.node7307 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7308
  · rfl
  · rfl
  · rfl
  · rfl

def B7306 : Block := .branch 138 ![385, 144115188075857410, 4750054613928474843140, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B7307, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1521).pointIds 1521)]
theorem treeEq7306 : B7306.tree = HexagonCover.NBand.M8300_8500.SplitData.node7306 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7307
  · rfl
  · rfl

def B7305 : Block := .branch 165 ![385, 144115188075857410, 4750054613928474843140, 1496577676626844588240652496863988076465268467982344, 89899879081576574539315864286613707321081872, 187072209578355573530071658587684226515959365894176, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1336).pointIds 1336), B7306, (.leaf 0 [] 0)]
theorem treeEq7305 : B7305.tree = HexagonCover.NBand.M8300_8500.SplitData.node7305 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7306
  · rfl

def B7304 : Block := .branch 167 ![385, 144115188075857410, 4750054613928474843140, 1496577676626844588240652496863988076465268467982344, 89899879081576574539315864286613707321081872, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1335).pointIds 1335), B7305, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7304 : B7304.tree = HexagonCover.NBand.M8300_8500.SplitData.node7304 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7305
  · rfl

def B7303 : Block := .branch 146 ![385, 144115188075857410, 4750054613928474843140, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B7304, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7303 : B7303.tree = HexagonCover.NBand.M8300_8500.SplitData.node7303 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7304
  · rfl
  · rfl

def B7302 : Block := .branch 170 ![385, 144115188075857410, 4750054613928474843140, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7303, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1334).pointIds 1334)]
theorem treeEq7302 : B7302.tree = HexagonCover.NBand.M8300_8500.SplitData.node7302 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7303
  · rfl
  · rfl
  · rfl

def B7301 : Block := .branch 172 ![385, 144185556820035074, 4750054613928474843140, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 38911019592319742682649828187563466705423972066394176] ![B7302, (.leaf 1 (Common.fact 1541).pointIds 1541), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), (.leaf 6 (Common.fact 1333).pointIds 1333)]
theorem treeEq7301 : B7301.tree = HexagonCover.NBand.M8300_8500.SplitData.node7301 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7302
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7300 : Block := .branch 174 ![385, 144185556820035074, 4750054613928474843140, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B7301]
theorem treeEq7300 : B7300.tree = HexagonCover.NBand.M8300_8500.SplitData.node7300 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7301

def B7299 : Block := .branch 139 ![385, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 98320, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B7300, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1326).pointIds 1326)]
theorem treeEq7299 : B7299.tree = HexagonCover.NBand.M8300_8500.SplitData.node7299 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7300
  · rfl
  · rfl

def B7298 : Block := .branch 147 ![385, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 98320, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7299, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1513).pointIds 1513)]
theorem treeEq7298 : B7298.tree = HexagonCover.NBand.M8300_8500.SplitData.node7298 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7299
  · rfl
  · rfl

def B7297 : Block := .branch 148 ![385, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 98320, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7298, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1325).pointIds 1325)]
theorem treeEq7297 : B7297.tree = HexagonCover.NBand.M8300_8500.SplitData.node7297 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7298
  · rfl
  · rfl

def B7296 : Block := .branch 173 ![2251799813685633, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1509).pointIds 1509), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7297]
theorem treeEq7296 : B7296.tree = HexagonCover.NBand.M8300_8500.SplitData.node7296 := by
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
  · exact treeEq7297

theorem accepted7296 : B7296.accepted = true := by decide +kernel
theorem checked7296 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7296 (maskNeeds ![2251799813685633, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq7296]
  exact B7296.sound accepted7296
#print axioms checked7296

end HexagonCover.NBand.M8300_8500.SplitTree.Run0102
