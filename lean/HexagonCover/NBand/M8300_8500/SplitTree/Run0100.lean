import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0099
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0100
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip7238_7239 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7239 ![385, 144115737831671298, 23630315257587698767876, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0099.checked7239
def B7264 : Block := .branch 129 ![385, 1538, 6148, 18889465931478580879368, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 1491).pointIds 1491), (.leaf 4 (Common.fact 1492).pointIds 1492), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1493).pointIds 1493)]
theorem treeEq7264 : B7264.tree = HexagonCover.NBand.M8300_8500.SplitData.node7264 := by
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

def B7263 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7264, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7263 : B7263.tree = HexagonCover.NBand.M8300_8500.SplitData.node7263 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7264
  · rfl
  · rfl

def B7262 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1516).pointIds 1516), (.leaf 2 (Common.fact 1517).pointIds 1517), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7263]
theorem treeEq7262 : B7262.tree = HexagonCover.NBand.M8300_8500.SplitData.node7262 := by
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
  · exact treeEq7263

def B7261 : Block := .branch 173 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7262, (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7261 : B7261.tree = HexagonCover.NBand.M8300_8500.SplitData.node7261 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7262
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7260 : Block := .branch 162 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7261]
theorem treeEq7260 : B7260.tree = HexagonCover.NBand.M8300_8500.SplitData.node7260 := by
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
  · exact treeEq7261

def B7259 : Block := .branch 165 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7260, (.leaf 0 [] 0)]
theorem treeEq7259 : B7259.tree = HexagonCover.NBand.M8300_8500.SplitData.node7259 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7260
  · rfl

def B7258 : Block := .branch 167 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7259, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7258 : B7258.tree = HexagonCover.NBand.M8300_8500.SplitData.node7258 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7259
  · rfl

def B7257 : Block := .branch 146 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7258, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7257 : B7257.tree = HexagonCover.NBand.M8300_8500.SplitData.node7257 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7258
  · rfl
  · rfl

def B7256 : Block := .branch 150 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7257, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7256 : B7256.tree = HexagonCover.NBand.M8300_8500.SplitData.node7256 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7257
  · rfl
  · rfl

def B7255 : Block := .branch 168 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7256, (.leaf 1 (Common.fact 1531).pointIds 1531), (.leaf 2 (Common.fact 1532).pointIds 1532), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7255 : B7255.tree = HexagonCover.NBand.M8300_8500.SplitData.node7255 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7256
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7254 : Block := .branch 170 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1519).pointIds 1519), (.leaf 2 (Common.fact 1520).pointIds 1520), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7255]
theorem treeEq7254 : B7254.tree = HexagonCover.NBand.M8300_8500.SplitData.node7254 := by
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
  · exact treeEq7255

def B7238 : Block := .branch 74 ![590295810358705652097, 144115737831671298, 4740849326109117913092, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), Tip7238_7239, B7254, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7238 : B7238.tree = HexagonCover.NBand.M8300_8500.SplitData.node7238 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7254
  · rfl
  · rfl
  · rfl

theorem accepted7238 : B7238.accepted = true := by decide +kernel
theorem checked7238 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7238 (maskNeeds ![590295810358705652097, 144115737831671298, 4740849326109117913092, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7238]
  exact B7238.sound accepted7238
#print axioms checked7238

def Tip7235_7238 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7238 ![590295810358705652097, 144115737831671298, 4740849326109117913092, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7238
def B7275 : Block := .branch 118 ![385, 1538, 6148, 79228171958997303332834402312, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1494).pointIds 1494), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1495).pointIds 1495)]
theorem treeEq7275 : B7275.tree = HexagonCover.NBand.M8300_8500.SplitData.node7275 := by
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

def B7274 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7275, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7274 : B7274.tree = HexagonCover.NBand.M8300_8500.SplitData.node7274 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7275
  · rfl
  · rfl

def B7273 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1516).pointIds 1516), (.leaf 2 (Common.fact 1517).pointIds 1517), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7274]
theorem treeEq7273 : B7273.tree = HexagonCover.NBand.M8300_8500.SplitData.node7273 := by
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
  · exact treeEq7274

def B7272 : Block := .branch 173 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7273, (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7272 : B7272.tree = HexagonCover.NBand.M8300_8500.SplitData.node7272 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7273
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7271 : Block := .branch 162 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7272]
theorem treeEq7271 : B7271.tree = HexagonCover.NBand.M8300_8500.SplitData.node7271 := by
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
  · exact treeEq7272

def B7270 : Block := .branch 165 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7271, (.leaf 0 [] 0)]
theorem treeEq7270 : B7270.tree = HexagonCover.NBand.M8300_8500.SplitData.node7270 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7271
  · rfl

def B7269 : Block := .branch 167 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7270, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7269 : B7269.tree = HexagonCover.NBand.M8300_8500.SplitData.node7269 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7270
  · rfl

def B7268 : Block := .branch 146 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7269, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7268 : B7268.tree = HexagonCover.NBand.M8300_8500.SplitData.node7268 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7269
  · rfl
  · rfl

def B7267 : Block := .branch 150 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7268, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7267 : B7267.tree = HexagonCover.NBand.M8300_8500.SplitData.node7267 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7268
  · rfl
  · rfl

def B7266 : Block := .branch 168 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7267, (.leaf 1 (Common.fact 1531).pointIds 1531), (.leaf 2 (Common.fact 1532).pointIds 1532), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7266 : B7266.tree = HexagonCover.NBand.M8300_8500.SplitData.node7266 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7267
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7265 : Block := .branch 170 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1519).pointIds 1519), (.leaf 2 (Common.fact 1520).pointIds 1520), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7266]
theorem treeEq7265 : B7265.tree = HexagonCover.NBand.M8300_8500.SplitData.node7265 := by
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
  · exact treeEq7266

def B7237 : Block := .branch 73 ![590295810358705652097, 144115737831671298, 4740849326109117913092, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), Tip7235_7238, B7265, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7237 : B7237.tree = HexagonCover.NBand.M8300_8500.SplitData.node7237 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7265
  · rfl
  · rfl
  · rfl

def B7277 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1497).pointIds 1497)]
theorem treeEq7277 : B7277.tree = HexagonCover.NBand.M8300_8500.SplitData.node7277 := by
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

def B7276 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7277, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1496).pointIds 1496)]
theorem treeEq7276 : B7276.tree = HexagonCover.NBand.M8300_8500.SplitData.node7276 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7277
  · rfl
  · rfl

def B7236 : Block := .branch 69 ![385, 144115737831671298, 4740849326109117913092, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7237, (.leaf 1 (Common.fact 158).pointIds 158), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B7276]
theorem treeEq7236 : B7236.tree = HexagonCover.NBand.M8300_8500.SplitData.node7236 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7237
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7276

def B7279 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1460).pointIds 1460)]
theorem treeEq7279 : B7279.tree = HexagonCover.NBand.M8300_8500.SplitData.node7279 := by
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

def B7278 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7279, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1498).pointIds 1498)]
theorem treeEq7278 : B7278.tree = HexagonCover.NBand.M8300_8500.SplitData.node7278 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7279
  · rfl
  · rfl

def B7235 : Block := .branch 67 ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 153).pointIds 153), B7236, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7278]
theorem treeEq7235 : B7235.tree = HexagonCover.NBand.M8300_8500.SplitData.node7235 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7236
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7278

theorem accepted7235 : B7235.accepted = true := by decide +kernel
theorem checked7235 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7235 (maskNeeds ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7235]
  exact B7235.sound accepted7235
#print axioms checked7235

def Tip7227_7235 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7235 ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7235
def B7230 : Block := .branch 79 ![288230376151712129, 144115737831671298, 6148, 24584, 98320, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1466).pointIds 1466)]
theorem treeEq7230 : B7230.tree = HexagonCover.NBand.M8300_8500.SplitData.node7230 := by
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

def B7229 : Block := .branch 173 ![288230376151712129, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1463).pointIds 1463), (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7230]
theorem treeEq7229 : B7229.tree = HexagonCover.NBand.M8300_8500.SplitData.node7229 := by
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
  · exact treeEq7230

def B7234 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7234 : B7234.tree = HexagonCover.NBand.M8300_8500.SplitData.node7234 := by
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

def B7233 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7234, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7233 : B7233.tree = HexagonCover.NBand.M8300_8500.SplitData.node7233 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7234
  · rfl
  · rfl

def B7232 : Block := .branch 173 ![576460752303423873, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1467).pointIds 1467), (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7233]
theorem treeEq7232 : B7232.tree = HexagonCover.NBand.M8300_8500.SplitData.node7232 := by
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
  · exact treeEq7233

def B7231 : Block := .branch 59 ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7232, Tip7227_7235, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7231 : B7231.tree = HexagonCover.NBand.M8300_8500.SplitData.node7231 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7232
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7228 : Block := .branch 58 ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7229, B7231, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq7228 : B7228.tree = HexagonCover.NBand.M8300_8500.SplitData.node7228 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7229
  · exact treeEq7231
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7291 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1498039178285958879553700154897116617114712060461120] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1506).pointIds 1506)]
theorem treeEq7291 : B7291.tree = HexagonCover.NBand.M8300_8500.SplitData.node7291 := by
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

def B7290 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154897116617114712060461120] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7291, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1505).pointIds 1505)]
theorem treeEq7290 : B7290.tree = HexagonCover.NBand.M8300_8500.SplitData.node7290 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7291
  · rfl
  · rfl

def B7289 : Block := .branch 75 ![385, 144115737831671298, 4740885354906136877060, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), (.leaf 2 (Common.fact 1504).pointIds 1504), (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7290]
theorem treeEq7289 : B7289.tree = HexagonCover.NBand.M8300_8500.SplitData.node7289 := by
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
  · exact treeEq7290

def B7288 : Block := .branch 82 ![385, 144115737831671298, 4740885354906136877060, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), (.leaf 2 (Common.fact 1503).pointIds 1503), B7289, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq7288 : B7288.tree = HexagonCover.NBand.M8300_8500.SplitData.node7288 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7289
  · rfl
  · rfl
  · rfl

def B7287 : Block := .branch 83 ![385, 144115737831671298, 4740885354906136877060, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), (.leaf 2 (Common.fact 1502).pointIds 1502), B7288, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq7287 : B7287.tree = HexagonCover.NBand.M8300_8500.SplitData.node7287 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7288
  · rfl
  · rfl
  · rfl

def B7286 : Block := .branch 84 ![385, 144115737831671298, 4740885354906136877060, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 1501).pointIds 1501), B7287, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq7286 : B7286.tree = HexagonCover.NBand.M8300_8500.SplitData.node7286 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7287
  · rfl
  · rfl
  · rfl

def B7285 : Block := .branch 161 ![385, 144115737831671298, 4740885354906136877060, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1500).pointIds 1500), (.leaf 3 (Common.fact 820).pointIds 820), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7286]
theorem treeEq7285 : B7285.tree = HexagonCover.NBand.M8300_8500.SplitData.node7285 := by
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
  · exact treeEq7286

def B7284 : Block := .branch 150 ![385, 144115737831671298, 4740885354906136877060, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7285, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7284 : B7284.tree = HexagonCover.NBand.M8300_8500.SplitData.node7284 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7285
  · rfl
  · rfl

def B7283 : Block := .branch 59 ![374144419156711147060143317175368453031918731002241, 144115737831671298, 4740885354906136877060, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 1018).pointIds 1018), B7284, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7283 : B7283.tree = HexagonCover.NBand.M8300_8500.SplitData.node7283 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7284
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7282 : Block := .branch 168 ![385, 144115737831671298, 4740885354906136877060, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1498039178285958879553700154859337685251754898751552] ![B7283, (.leaf 1 (Common.fact 1531).pointIds 1531), (.leaf 2 (Common.fact 1532).pointIds 1532), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7282 : B7282.tree = HexagonCover.NBand.M8300_8500.SplitData.node7282 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7283
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7281 : Block := .branch 170 ![385, 144115737831671298, 4740885354906136877060, 81208905262747173701516139716616, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1519).pointIds 1519), (.leaf 2 (Common.fact 1520).pointIds 1520), (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7282]
theorem treeEq7281 : B7281.tree = HexagonCover.NBand.M8300_8500.SplitData.node7281 := by
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
  · exact treeEq7282

def B7280 : Block := .branch 85 ![385, 144115737831671298, 4740885354906136877060, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 1499).pointIds 1499), B7281, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7280 : B7280.tree = HexagonCover.NBand.M8300_8500.SplitData.node7280 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7281
  · rfl
  · rfl
  · rfl

def B7227 : Block := .branch 56 ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 121).pointIds 121), B7228, B7280, (.leaf 3 (Common.fact 123).pointIds 123), (.leaf 4 (Common.fact 124).pointIds 124), (.leaf 5 (Common.fact 125).pointIds 125), (.leaf 6 (Common.fact 126).pointIds 126)]
theorem treeEq7227 : B7227.tree = HexagonCover.NBand.M8300_8500.SplitData.node7227 := by
  change Tree.branch (56 : Fin 177) _ = Tree.branch (56 : Fin 177) _
  apply congrArg (Tree.branch (56 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7228
  · exact treeEq7280
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted7227 : B7227.accepted = true := by decide +kernel
theorem checked7227 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7227 (maskNeeds ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7227]
  exact B7227.sound accepted7227
#print axioms checked7227

def B7171 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 1223).pointIds 1223)]
theorem treeEq7171 : B7171.tree = HexagonCover.NBand.M8300_8500.SplitData.node7171 := by
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

def B7170 : Block := .branch 169 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38913942595572621100091312355903751681359409644568640] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1525).pointIds 1525), (.leaf 2 (Common.fact 1526).pointIds 1526), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7171, (.leaf 6 (Common.fact 1527).pointIds 1527)]
theorem treeEq7170 : B7170.tree = HexagonCover.NBand.M8300_8500.SplitData.node7170 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7171
  · rfl

def B7169 : Block := .branch 161 ![385, 144115737831671298, 116061619496301712870742020, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1524).pointIds 1524), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7170]
theorem treeEq7169 : B7169.tree = HexagonCover.NBand.M8300_8500.SplitData.node7169 := by
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
  · exact treeEq7170

def B7168 : Block := .branch 85 ![385, 144115737831671298, 77375993268633579280144388, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B7169, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7168 : B7168.tree = HexagonCover.NBand.M8300_8500.SplitData.node7168 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7169
  · rfl
  · rfl
  · rfl
  · rfl

def B7167 : Block := .branch 66 ![385, 144115737831671298, 77375993268633579280144388, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 148).pointIds 148), B7168, (.leaf 2 (Common.fact 1522).pointIds 1522), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1523).pointIds 1523)]
theorem treeEq7167 : B7167.tree = HexagonCover.NBand.M8300_8500.SplitData.node7167 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7168
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7166 : Block := .branch 86 ![385, 144115737831671298, 4740813297312098949124, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B7167, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1346).pointIds 1346)]
theorem treeEq7166 : B7166.tree = HexagonCover.NBand.M8300_8500.SplitData.node7166 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7167
  · rfl
  · rfl
  · rfl
  · rfl

def B7165 : Block := .branch 138 ![385, 144115737831671298, 4740813297312098949124, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 233840261972944466912589573234605283144949207269408, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B7166, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1521).pointIds 1521)]
theorem treeEq7165 : B7165.tree = HexagonCover.NBand.M8300_8500.SplitData.node7165 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7166
  · rfl
  · rfl

def B7164 : Block := .branch 165 ![385, 144115737831671298, 4740813297312098949124, 1496577676626844588240652496863988076465268467982344, 89899879081576574539315864286613707321081872, 187072209578355573530071658587684226515959365894176, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1336).pointIds 1336), B7165, (.leaf 0 [] 0)]
theorem treeEq7164 : B7164.tree = HexagonCover.NBand.M8300_8500.SplitData.node7164 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7165
  · rfl

def B7163 : Block := .branch 167 ![385, 144115737831671298, 4740813297312098949124, 1496577676626844588240652496863988076465268467982344, 89899879081576574539315864286613707321081872, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1335).pointIds 1335), B7164, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7163 : B7163.tree = HexagonCover.NBand.M8300_8500.SplitData.node7163 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7164
  · rfl

def B7162 : Block := .branch 146 ![385, 144115737831671298, 4740813297312098949124, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B7163, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7162 : B7162.tree = HexagonCover.NBand.M8300_8500.SplitData.node7162 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7163
  · rfl
  · rfl

def B7161 : Block := .branch 170 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1519).pointIds 1519), (.leaf 2 (Common.fact 1520).pointIds 1520), B7162, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1334).pointIds 1334)]
theorem treeEq7161 : B7161.tree = HexagonCover.NBand.M8300_8500.SplitData.node7161 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7162
  · rfl
  · rfl
  · rfl

def B7160 : Block := .branch 172 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 38911019592319742682649828187563466705423972066394176] ![B7161, (.leaf 1 (Common.fact 1516).pointIds 1516), (.leaf 2 (Common.fact 1517).pointIds 1517), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), (.leaf 6 (Common.fact 1333).pointIds 1333)]
theorem treeEq7160 : B7160.tree = HexagonCover.NBand.M8300_8500.SplitData.node7160 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7161
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7159 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B7160]
theorem treeEq7159 : B7159.tree = HexagonCover.NBand.M8300_8500.SplitData.node7159 := by
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
  · exact treeEq7160

def B7158 : Block := .branch 139 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 98320, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B7159, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1326).pointIds 1326)]
theorem treeEq7158 : B7158.tree = HexagonCover.NBand.M8300_8500.SplitData.node7158 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7159
  · rfl
  · rfl

def B7157 : Block := .branch 147 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 98320, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7158, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1513).pointIds 1513)]
theorem treeEq7157 : B7157.tree = HexagonCover.NBand.M8300_8500.SplitData.node7157 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7158
  · rfl
  · rfl

def B7156 : Block := .branch 148 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 98320, 393248, 14965776766290229270800655888339885711381173282275392] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7157, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1325).pointIds 1325)]
theorem treeEq7156 : B7156.tree = HexagonCover.NBand.M8300_8500.SplitData.node7156 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7157
  · rfl
  · rfl

def B7155 : Block := .branch 173 ![2251799813685633, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1509).pointIds 1509), (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7156]
theorem treeEq7155 : B7155.tree = HexagonCover.NBand.M8300_8500.SplitData.node7155 := by
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
  · exact treeEq7156

theorem accepted7155 : B7155.accepted = true := by decide +kernel
theorem checked7155 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7155 (maskNeeds ![2251799813685633, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq7155]
  exact B7155.sound accepted7155
#print axioms checked7155

end HexagonCover.NBand.M8300_8500.SplitTree.Run0100
