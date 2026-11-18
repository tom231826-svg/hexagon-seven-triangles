import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0104
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0105
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip7456_7576 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7576 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 4731607940223509469188, 237708666059185305364125999112, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] HexagonCover.NBand.M8300_8500.SplitTree.Run0104.checked7576
def Tip7456_7553 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7553 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 9713917096720214068828164, 237689323246071471297330700296, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] HexagonCover.NBand.M8300_8500.SplitTree.Run0104.checked7553
def Tip7456_7459 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7459 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 4878213818261697370003460, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] HexagonCover.NBand.M8300_8500.SplitTree.Run0104.checked7459
def B7575 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202982787964486243516682446304036444536848, 393248, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1661).pointIds 1661), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1665).pointIds 1665)]
theorem treeEq7575 : B7575.tree = HexagonCover.NBand.M8300_8500.SplitData.node7575 := by
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

def B7574 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202982123350488351058745994400506304364560, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 899).pointIds 899), B7575, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1594).pointIds 1594)]
theorem treeEq7574 : B7574.tree = HexagonCover.NBand.M8300_8500.SplitData.node7574 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7575
  · rfl
  · rfl

def B7573 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202982123350488351058745994400506304364560, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 898).pointIds 898), B7574, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1597).pointIds 1597)]
theorem treeEq7573 : B7573.tree = HexagonCover.NBand.M8300_8500.SplitData.node7573 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7574
  · rfl
  · rfl

def B7572 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202982123350488351058745994400506304364560, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 897).pointIds 897), B7573, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1605).pointIds 1605)]
theorem treeEq7572 : B7572.tree = HexagonCover.NBand.M8300_8500.SplitData.node7572 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7573
  · rfl
  · rfl

def B7571 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202982123350488351058745994400506304364560, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 760).pointIds 760), B7572, (.leaf 0 [] 0)]
theorem treeEq7571 : B7571.tree = HexagonCover.NBand.M8300_8500.SplitData.node7571 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7572
  · rfl

def B7570 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202982123350488351058745994400506304364560, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 759).pointIds 759), B7571, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7570 : B7570.tree = HexagonCover.NBand.M8300_8500.SplitData.node7570 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7571
  · rfl

def B7569 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 1329227995784915872903807060280442896, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 896).pointIds 896), B7570, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7569 : B7569.tree = HexagonCover.NBand.M8300_8500.SplitData.node7569 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7570
  · rfl
  · rfl

def B7568 : Block := .branch 170 ![385, 144115188075857410, 4731607869854765291524, 14507109835375550096498696, 1329227995784915872903807060280442896, 393248, 84182494310281791476927169565783049522286138517618752] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7569, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1643).pointIds 1643)]
theorem treeEq7568 : B7568.tree = HexagonCover.NBand.M8300_8500.SplitData.node7568 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7569
  · rfl
  · rfl
  · rfl

def B7567 : Block := .branch 175 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 19385323653637247466477572, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 1654).pointIds 1654), (.leaf 1 (Common.fact 1638).pointIds 1638), (.leaf 2 (Common.fact 1668).pointIds 1668), (.leaf 3 (Common.fact 1664).pointIds 1664), (.leaf 4 (Common.fact 1656).pointIds 1656), (.leaf 5 (Common.fact 1646).pointIds 1646), B7568]
theorem treeEq7567 : B7567.tree = HexagonCover.NBand.M8300_8500.SplitData.node7567 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7568

def B7566 : Block := .branch 84 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 42510539803180671178756, 237698994652628388330728349704, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B7567, Tip7456_7576, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq7566 : B7566.tree = HexagonCover.NBand.M8300_8500.SplitData.node7566 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7567
  · rfl
  · rfl
  · rfl
  · rfl

def B7552 : Block := .branch 83 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 42510539803180671178756, 237689323246071471297330700296, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip7456_7553, B7566, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq7552 : B7552.tree = HexagonCover.NBand.M8300_8500.SplitData.node7552 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7566
  · rfl
  · rfl
  · rfl

def B7458 : Block := .branch 82 ![618970019644941937263247745, 1461501637330902918203684832716463163641027364354, 42510539803180671178756, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), Tip7456_7459, B7552, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq7458 : B7458.tree = HexagonCover.NBand.M8300_8500.SplitData.node7458 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7552
  · rfl
  · rfl
  · rfl

def B7618 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 1644).pointIds 1644)]
theorem treeEq7618 : B7618.tree = HexagonCover.NBand.M8300_8500.SplitData.node7618 := by
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

def B7617 : Block := .branch 169 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 84185417313534669894368653734123334498221576095793216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1547).pointIds 1547), (.leaf 2 (Common.fact 1548).pointIds 1548), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), B7618, (.leaf 6 (Common.fact 1599).pointIds 1599)]
theorem treeEq7617 : B7617.tree = HexagonCover.NBand.M8300_8500.SplitData.node7617 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7618
  · rfl

def B7616 : Block := .branch 161 ![385, 144115188075857410, 95780971304118053647396689196936834551932804082440196, 1496577676626844588240652496863988076465268467982344, 696898287454081973172991196020261297160208, 393248, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1722).pointIds 1722), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7617]
theorem treeEq7616 : B7616.tree = HexagonCover.NBand.M8300_8500.SplitData.node7616 := by
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
  · exact treeEq7617

def B7615 : Block := .branch 176 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 42510575761608945965060, 1496577676626844588240652496863988076465268467982344, 696899616682077758088864099827321577504784, 393248, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 1710).pointIds 1710), (.leaf 1 (Common.fact 1717).pointIds 1717), B7616, (.leaf 3 (Common.fact 1718).pointIds 1718), (.leaf 4 (Common.fact 1719).pointIds 1719), (.leaf 5 (Common.fact 1720).pointIds 1720), (.leaf 6 (Common.fact 1721).pointIds 1721)]
theorem treeEq7615 : B7615.tree = HexagonCover.NBand.M8300_8500.SplitData.node7615 := by
  change Tree.branch (176 : Fin 177) _ = Tree.branch (176 : Fin 177) _
  apply congrArg (Tree.branch (176 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7616
  · rfl
  · rfl
  · rfl
  · rfl

def B7614 : Block := .branch 170 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 42510575761608945965060, 79228162514264337593543974920, 696899616682077758088864099827321577504784, 393248, 84182494310260008088532246364457901932182264230707264] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), B7615, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1643).pointIds 1643)]
theorem treeEq7614 : B7614.tree = HexagonCover.NBand.M8300_8500.SplitData.node7614 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7615
  · rfl
  · rfl
  · rfl

def B7613 : Block := .branch 175 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 42510575761608945965060, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658200981264833901766010739944096666662469696] ![(.leaf 0 (Common.fact 1654).pointIds 1654), (.leaf 1 (Common.fact 1714).pointIds 1714), (.leaf 2 (Common.fact 1715).pointIds 1715), (.leaf 3 (Common.fact 1716).pointIds 1716), (.leaf 4 (Common.fact 1656).pointIds 1656), (.leaf 5 (Common.fact 1646).pointIds 1646), B7614]
theorem treeEq7613 : B7613.tree = HexagonCover.NBand.M8300_8500.SplitData.node7613 := by
  change Tree.branch (175 : Fin 177) _ = Tree.branch (175 : Fin 177) _
  apply congrArg (Tree.branch (175 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7614

def B7457 : Block := .branch 55 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 42510539803180671178756, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 36292008658222764653228824967335887534200540949381184] ![(.leaf 0 (Common.fact 133).pointIds 133), B7458, B7613, (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 137).pointIds 137)]
theorem treeEq7457 : B7457.tree = HexagonCover.NBand.M8300_8500.SplitData.node7457 := by
  change Tree.branch (55 : Fin 177) _ = Tree.branch (55 : Fin 177) _
  apply congrArg (Tree.branch (55 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7458
  · exact treeEq7613
  · rfl
  · rfl
  · rfl
  · rfl

def B7456 : Block := .branch 168 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 42510539803180671178756, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), B7457]
theorem treeEq7456 : B7456.tree = HexagonCover.NBand.M8300_8500.SplitData.node7456 := by
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
  · exact treeEq7457

theorem accepted7456 : B7456.accepted = true := by decide +kernel
theorem checked7456 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7456 (maskNeeds ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 42510539803180671178756, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 35917864239066053506168681650160519081168622218379328]) := by
  rw [← treeEq7456]
  exact B7456.sound accepted7456
#print axioms checked7456

def B7641 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7641 : B7641.tree = HexagonCover.NBand.M8300_8500.SplitData.node7641 := by
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

def B7640 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7641, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7640 : B7640.tree = HexagonCover.NBand.M8300_8500.SplitData.node7640 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7641
  · rfl
  · rfl

def B7639 : Block := .branch 173 ![604462909807314587353473, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7640]
theorem treeEq7639 : B7639.tree = HexagonCover.NBand.M8300_8500.SplitData.node7639 := by
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
  · exact treeEq7640

def B7643 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1473).pointIds 1473)]
theorem treeEq7643 : B7643.tree = HexagonCover.NBand.M8300_8500.SplitData.node7643 := by
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

def B7642 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7643, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1472).pointIds 1472)]
theorem treeEq7642 : B7642.tree = HexagonCover.NBand.M8300_8500.SplitData.node7642 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7643
  · rfl
  · rfl

def B7638 : Block := .branch 79 ![385, 182395784908506626, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7639, (.leaf 1 (Common.fact 1726).pointIds 1726), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B7642]
theorem treeEq7638 : B7638.tree = HexagonCover.NBand.M8300_8500.SplitData.node7638 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7639
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7642

def B7645 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1476).pointIds 1476)]
theorem treeEq7645 : B7645.tree = HexagonCover.NBand.M8300_8500.SplitData.node7645 := by
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

def B7644 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7645, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1474).pointIds 1474)]
theorem treeEq7644 : B7644.tree = HexagonCover.NBand.M8300_8500.SplitData.node7644 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7645
  · rfl
  · rfl

def B7637 : Block := .branch 77 ![385, 182395784908506626, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 163).pointIds 163), B7638, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7644]
theorem treeEq7637 : B7637.tree = HexagonCover.NBand.M8300_8500.SplitData.node7637 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7638
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7644

def B7647 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1478).pointIds 1478)]
theorem treeEq7647 : B7647.tree = HexagonCover.NBand.M8300_8500.SplitData.node7647 := by
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

def B7646 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7647, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1477).pointIds 1477)]
theorem treeEq7646 : B7646.tree = HexagonCover.NBand.M8300_8500.SplitData.node7646 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7647
  · rfl
  · rfl

def B7636 : Block := .branch 75 ![385, 182395784908506626, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B7637, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7646]
theorem treeEq7636 : B7636.tree = HexagonCover.NBand.M8300_8500.SplitData.node7636 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7637
  · rfl
  · rfl
  · rfl
  · exact treeEq7646

def B7649 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7649 : B7649.tree = HexagonCover.NBand.M8300_8500.SplitData.node7649 := by
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

def B7648 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7649, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1479).pointIds 1479)]
theorem treeEq7648 : B7648.tree = HexagonCover.NBand.M8300_8500.SplitData.node7648 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7649
  · rfl
  · rfl

def B7635 : Block := .branch 66 ![385, 182395784908506626, 23639520615775799875588, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 148).pointIds 148), B7636, (.leaf 2 (Common.fact 1728).pointIds 1728), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7648]
theorem treeEq7635 : B7635.tree = HexagonCover.NBand.M8300_8500.SplitData.node7635 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7636
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7648

theorem accepted7635 : B7635.accepted = true := by decide +kernel
theorem checked7635 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7635 (maskNeeds ![385, 182395784908506626, 23639520615775799875588, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7635]
  exact B7635.sound accepted7635
#print axioms checked7635

def Tip7634_7635 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7635 ![385, 182395784908506626, 23639520615775799875588, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7635
def B7660 : Block := .branch 129 ![385, 1538, 6148, 18889465931478580879368, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 1491).pointIds 1491), (.leaf 4 (Common.fact 1492).pointIds 1492), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1493).pointIds 1493)]
theorem treeEq7660 : B7660.tree = HexagonCover.NBand.M8300_8500.SplitData.node7660 := by
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

def B7659 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7660, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7659 : B7659.tree = HexagonCover.NBand.M8300_8500.SplitData.node7659 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7660
  · rfl
  · rfl

def B7658 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1729).pointIds 1729), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7659]
theorem treeEq7658 : B7658.tree = HexagonCover.NBand.M8300_8500.SplitData.node7658 := by
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
  · exact treeEq7659

def B7657 : Block := .branch 173 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7658, (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7657 : B7657.tree = HexagonCover.NBand.M8300_8500.SplitData.node7657 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7658
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7656 : Block := .branch 162 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7657]
theorem treeEq7656 : B7656.tree = HexagonCover.NBand.M8300_8500.SplitData.node7656 := by
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
  · exact treeEq7657

def B7655 : Block := .branch 165 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7656, (.leaf 0 [] 0)]
theorem treeEq7655 : B7655.tree = HexagonCover.NBand.M8300_8500.SplitData.node7655 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7656
  · rfl

def B7654 : Block := .branch 167 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7655, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7654 : B7654.tree = HexagonCover.NBand.M8300_8500.SplitData.node7654 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7655
  · rfl

def B7653 : Block := .branch 146 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7654, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7653 : B7653.tree = HexagonCover.NBand.M8300_8500.SplitData.node7653 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7654
  · rfl
  · rfl

def B7652 : Block := .branch 150 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7653, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7652 : B7652.tree = HexagonCover.NBand.M8300_8500.SplitData.node7652 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7653
  · rfl
  · rfl

def B7651 : Block := .branch 168 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7652, (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7651 : B7651.tree = HexagonCover.NBand.M8300_8500.SplitData.node7651 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7652
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7650 : Block := .branch 170 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228181403730269072124829704, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7651]
theorem treeEq7650 : B7650.tree = HexagonCover.NBand.M8300_8500.SplitData.node7650 := by
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
  · exact treeEq7651

def B7634 : Block := .branch 74 ![590295810358705652097, 182395784908506626, 4750054684297219020804, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), Tip7634_7635, B7650, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7634 : B7634.tree = HexagonCover.NBand.M8300_8500.SplitData.node7634 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7650
  · rfl
  · rfl
  · rfl

theorem accepted7634 : B7634.accepted = true := by decide +kernel
theorem checked7634 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7634 (maskNeeds ![590295810358705652097, 182395784908506626, 4750054684297219020804, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7634]
  exact B7634.sound accepted7634
#print axioms checked7634

def Tip7631_7634 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7634 ![590295810358705652097, 182395784908506626, 4750054684297219020804, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7634
def B7671 : Block := .branch 118 ![385, 1538, 6148, 79228171958997303332834402312, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1494).pointIds 1494), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1495).pointIds 1495)]
theorem treeEq7671 : B7671.tree = HexagonCover.NBand.M8300_8500.SplitData.node7671 := by
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

def B7670 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7671, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7670 : B7670.tree = HexagonCover.NBand.M8300_8500.SplitData.node7670 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7671
  · rfl
  · rfl

def B7669 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1729).pointIds 1729), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7670]
theorem treeEq7669 : B7669.tree = HexagonCover.NBand.M8300_8500.SplitData.node7669 := by
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
  · exact treeEq7670

def B7668 : Block := .branch 173 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7669, (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7668 : B7668.tree = HexagonCover.NBand.M8300_8500.SplitData.node7668 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7669
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7667 : Block := .branch 162 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7668]
theorem treeEq7667 : B7667.tree = HexagonCover.NBand.M8300_8500.SplitData.node7667 := by
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
  · exact treeEq7668

def B7666 : Block := .branch 165 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7667, (.leaf 0 [] 0)]
theorem treeEq7666 : B7666.tree = HexagonCover.NBand.M8300_8500.SplitData.node7666 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7667
  · rfl

def B7665 : Block := .branch 167 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7666, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7665 : B7665.tree = HexagonCover.NBand.M8300_8500.SplitData.node7665 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7666
  · rfl

def B7664 : Block := .branch 146 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7665, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7664 : B7664.tree = HexagonCover.NBand.M8300_8500.SplitData.node7664 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7665
  · rfl
  · rfl

def B7663 : Block := .branch 150 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7664, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7663 : B7663.tree = HexagonCover.NBand.M8300_8500.SplitData.node7663 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7664
  · rfl
  · rfl

def B7662 : Block := .branch 168 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7663, (.leaf 1 (Common.fact 1554).pointIds 1554), (.leaf 2 (Common.fact 1555).pointIds 1555), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7662 : B7662.tree = HexagonCover.NBand.M8300_8500.SplitData.node7662 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7663
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7661 : Block := .branch 170 ![590295810358705652097, 182395784908506626, 4731607869854765291524, 79228171958997303332834402312, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7662]
theorem treeEq7661 : B7661.tree = HexagonCover.NBand.M8300_8500.SplitData.node7661 := by
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
  · exact treeEq7662

def B7633 : Block := .branch 73 ![590295810358705652097, 182395784908506626, 4750054684297219020804, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), Tip7631_7634, B7661, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7633 : B7633.tree = HexagonCover.NBand.M8300_8500.SplitData.node7633 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7661
  · rfl
  · rfl
  · rfl

def B7673 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1497).pointIds 1497)]
theorem treeEq7673 : B7673.tree = HexagonCover.NBand.M8300_8500.SplitData.node7673 := by
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

def B7672 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7673, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1496).pointIds 1496)]
theorem treeEq7672 : B7672.tree = HexagonCover.NBand.M8300_8500.SplitData.node7672 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7673
  · rfl
  · rfl

def B7632 : Block := .branch 69 ![385, 182395784908506626, 4750054684297219020804, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7633, (.leaf 1 (Common.fact 1727).pointIds 1727), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B7672]
theorem treeEq7632 : B7632.tree = HexagonCover.NBand.M8300_8500.SplitData.node7632 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7633
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7672

def B7675 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1460).pointIds 1460)]
theorem treeEq7675 : B7675.tree = HexagonCover.NBand.M8300_8500.SplitData.node7675 := by
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

def B7674 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7675, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1498).pointIds 1498)]
theorem treeEq7674 : B7674.tree = HexagonCover.NBand.M8300_8500.SplitData.node7674 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7675
  · rfl
  · rfl

def B7631 : Block := .branch 67 ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 153).pointIds 153), B7632, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7674]
theorem treeEq7631 : B7631.tree = HexagonCover.NBand.M8300_8500.SplitData.node7631 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7632
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7674

theorem accepted7631 : B7631.accepted = true := by decide +kernel
theorem checked7631 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7631 (maskNeeds ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7631]
  exact B7631.sound accepted7631
#print axioms checked7631

end HexagonCover.NBand.M8300_8500.SplitTree.Run0105
