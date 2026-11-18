import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0099
import HexagonCover.NBand.M8300_8500.SplitTree.Run0100
import HexagonCover.NBand.M8300_8500.SplitTree.Run0101
import HexagonCover.NBand.M8300_8500.SplitTree.Run0102
import HexagonCover.NBand.M8300_8500.SplitTree.Run0105
import HexagonCover.NBand.M8300_8500.SplitTree.Run0106
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0107
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip7436_7456 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7456 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 42510539803180671178756, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 35917864239066053506168681650160519081168622218379328] HexagonCover.NBand.M8300_8500.SplitTree.Run0105.checked7456
def B7455 : Block := .branch 75 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 237684487542793012780631875592, 696899616682077758088864099827321577504784, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), Tip7436_7456, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), (.leaf 6 (Common.fact 1589).pointIds 1589)]
theorem treeEq7455 : B7455.tree = HexagonCover.NBand.M8300_8500.SplitData.node7455 := by
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
  · rfl

def B7454 : Block := .branch 97 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696899616682077758088864099827321577504784, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B7455, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 1588).pointIds 1588)]
theorem treeEq7454 : B7454.tree = HexagonCover.NBand.M8300_8500.SplitData.node7454 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7455
  · rfl
  · rfl
  · rfl

def B7453 : Block := .branch 120 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B7454, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1587).pointIds 1587)]
theorem treeEq7453 : B7453.tree = HexagonCover.NBand.M8300_8500.SplitData.node7453 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7454
  · rfl
  · rfl

def B7452 : Block := .branch 74 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 162338504991727627729171554263048, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), B7453, (.leaf 3 (Common.fact 1037).pointIds 1037), (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7452 : B7452.tree = HexagonCover.NBand.M8300_8500.SplitData.node7452 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7453
  · rfl
  · rfl
  · rfl
  · rfl

def B7451 : Block := .branch 107 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 699620546389449480880698192879715442851856, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B7452, (.leaf 4 (Common.fact 1585).pointIds 1585), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 1586).pointIds 1586)]
theorem treeEq7451 : B7451.tree = HexagonCover.NBand.M8300_8500.SplitData.node7451 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7452
  · rfl
  · rfl
  · rfl

def B7450 : Block := .branch 73 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 332307078174391482490289358614061064, 699620546389449480880698192879715442851856, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), B7451, (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7450 : B7450.tree = HexagonCover.NBand.M8300_8500.SplitData.node7450 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7451
  · rfl
  · rfl
  · rfl
  · rfl

def B7449 : Block := .branch 118 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 699620546389449480880698192879715442851856, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B7450, (.leaf 4 (Common.fact 1583).pointIds 1583), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1584).pointIds 1584)]
theorem treeEq7449 : B7449.tree = HexagonCover.NBand.M8300_8500.SplitData.node7449 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7450
  · rfl
  · rfl
  · rfl

def B7448 : Block := .branch 128 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 699620546389449480880698192879715442851856, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B7449, (.leaf 4 (Common.fact 1581).pointIds 1581), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1582).pointIds 1582)]
theorem treeEq7448 : B7448.tree = HexagonCover.NBand.M8300_8500.SplitData.node7448 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7449
  · rfl
  · rfl
  · rfl

def B7447 : Block := .branch 131 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 729).pointIds 729), (.leaf 1 (Common.fact 730).pointIds 730), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), B7448, (.leaf 5 (Common.fact 733).pointIds 733), (.leaf 6 (Common.fact 1580).pointIds 1580)]
theorem treeEq7447 : B7447.tree = HexagonCover.NBand.M8300_8500.SplitData.node7447 := by
  change Tree.branch (131 : Fin 177) _ = Tree.branch (131 : Fin 177) _
  apply congrArg (Tree.branch (131 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7448
  · rfl
  · rfl

def B7446 : Block := .branch 140 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B7447, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 1579).pointIds 1579)]
theorem treeEq7446 : B7446.tree = HexagonCover.NBand.M8300_8500.SplitData.node7446 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7447
  · rfl
  · rfl

def B7445 : Block := .branch 64 ![618970019644941937263247745, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 1578).pointIds 1578), B7446, (.leaf 3 (Common.fact 90).pointIds 90), (.leaf 4 (Common.fact 91).pointIds 91), (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 93).pointIds 93)]
theorem treeEq7445 : B7445.tree = HexagonCover.NBand.M8300_8500.SplitData.node7445 := by
  change Tree.branch (64 : Fin 177) _ = Tree.branch (64 : Fin 177) _
  apply congrArg (Tree.branch (64 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7446
  · rfl
  · rfl
  · rfl
  · rfl

def B7444 : Block := .branch 89 ![2251799813685633, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![B7445, (.leaf 1 (Common.fact 1576).pointIds 1576), (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 1577).pointIds 1577)]
theorem treeEq7444 : B7444.tree = HexagonCover.NBand.M8300_8500.SplitData.node7444 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7445
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7443 : Block := .branch 90 ![2251799813685633, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![B7444, (.leaf 1 (Common.fact 1574).pointIds 1574), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), (.leaf 6 (Common.fact 1575).pointIds 1575)]
theorem treeEq7443 : B7443.tree = HexagonCover.NBand.M8300_8500.SplitData.node7443 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7444
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7442 : Block := .branch 172 ![2251799813685633, 1461501637330902918203684832716427134844008400386, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![B7443, (.leaf 1 (Common.fact 1572).pointIds 1572), (.leaf 2 (Common.fact 1542).pointIds 1542), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), (.leaf 6 (Common.fact 1573).pointIds 1573)]
theorem treeEq7442 : B7442.tree = HexagonCover.NBand.M8300_8500.SplitData.node7442 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7443
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7441 : Block := .branch 160 ![2251799813685633, 144115188075857410, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 35917864239066053506168681650160519081168622218379328] ![(.leaf 0 (Common.fact 347).pointIds 347), B7442, (.leaf 2 (Common.fact 1550).pointIds 1550), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1571).pointIds 1571)]
theorem treeEq7441 : B7441.tree = HexagonCover.NBand.M8300_8500.SplitData.node7441 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7442
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7440 : Block := .branch 174 ![2251799813685633, 144115188075857410, 4731607940223509469188, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B7441]
theorem treeEq7440 : B7440.tree = HexagonCover.NBand.M8300_8500.SplitData.node7440 := by
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
  · exact treeEq7441

def B7439 : Block := .branch 139 ![2251799813685633, 144115188075857410, 4731607940223509469188, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B7440, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1570).pointIds 1570)]
theorem treeEq7439 : B7439.tree = HexagonCover.NBand.M8300_8500.SplitData.node7439 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7440
  · rfl
  · rfl

def B7438 : Block := .branch 147 ![2251799813685633, 144115188075857410, 4731607940223509469188, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7439, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1569).pointIds 1569)]
theorem treeEq7438 : B7438.tree = HexagonCover.NBand.M8300_8500.SplitData.node7438 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7439
  · rfl
  · rfl

def B7437 : Block := .branch 148 ![2251799813685633, 144115188075857410, 4731607940223509469188, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7438, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1568).pointIds 1568)]
theorem treeEq7437 : B7437.tree = HexagonCover.NBand.M8300_8500.SplitData.node7437 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7438
  · rfl
  · rfl

def B7436 : Block := .branch 173 ![2251799813685633, 144115188075857410, 4731607940223509469188, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1509).pointIds 1509), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7437]
theorem treeEq7436 : B7436.tree = HexagonCover.NBand.M8300_8500.SplitData.node7436 := by
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
  · exact treeEq7437

theorem accepted7436 : B7436.accepted = true := by decide +kernel
theorem checked7436 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7436 (maskNeeds ![2251799813685633, 144115188075857410, 4731607940223509469188, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq7436]
  exact B7436.sound accepted7436
#print axioms checked7436

def Tip7619_7631 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7631 ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0105.checked7631
def Tip7619_7684 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7684 ![385, 506795695567537666, 4750090642725493807108, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0106.checked7684
def Tip7619_7742 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7742 ![385, 146507725377897986, 4750126671522512771076, 79228162514264337593543974920, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0106.checked7742
def B7626 : Block := .branch 79 ![288230376151712129, 182395784908506626, 6148, 24584, 98320, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 1726).pointIds 1726), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1466).pointIds 1466)]
theorem treeEq7626 : B7626.tree = HexagonCover.NBand.M8300_8500.SplitData.node7626 := by
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

def B7625 : Block := .branch 173 ![288230376151712129, 182395784908506626, 4731607869854765291524, 79228162514264337593543974920, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1463).pointIds 1463), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7626]
theorem treeEq7625 : B7625.tree = HexagonCover.NBand.M8300_8500.SplitData.node7625 := by
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
  · exact treeEq7626

def B7630 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7630 : B7630.tree = HexagonCover.NBand.M8300_8500.SplitData.node7630 := by
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

def B7629 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7630, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7629 : B7629.tree = HexagonCover.NBand.M8300_8500.SplitData.node7629 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7630
  · rfl
  · rfl

def B7628 : Block := .branch 173 ![576460752303423873, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1467).pointIds 1467), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7629]
theorem treeEq7628 : B7628.tree = HexagonCover.NBand.M8300_8500.SplitData.node7628 := by
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
  · exact treeEq7629

def B7627 : Block := .branch 59 ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7628, Tip7619_7631, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7627 : B7627.tree = HexagonCover.NBand.M8300_8500.SplitData.node7627 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7628
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7624 : Block := .branch 58 ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7625, B7627, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq7624 : B7624.tree = HexagonCover.NBand.M8300_8500.SplitData.node7624 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7625
  · exact treeEq7627
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7623 : Block := .branch 147 ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7624, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1462).pointIds 1462)]
theorem treeEq7623 : B7623.tree = HexagonCover.NBand.M8300_8500.SplitData.node7623 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7624
  · rfl
  · rfl

def B7622 : Block := .branch 160 ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1725).pointIds 1725), (.leaf 2 (Common.fact 1550).pointIds 1550), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B7623]
theorem treeEq7622 : B7622.tree = HexagonCover.NBand.M8300_8500.SplitData.node7622 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7623

def B7621 : Block := .branch 171 ![385, 182395784908506626, 4750054684297219020804, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1008).pointIds 1008), (.leaf 1 (Common.fact 1724).pointIds 1724), (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), B7622]
theorem treeEq7621 : B7621.tree = HexagonCover.NBand.M8300_8500.SplitData.node7621 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7622

def B7683 : Block := .branch 79 ![288230376151712129, 218424581927470594, 6148, 24584, 98320, 393248, 35917864239044270117773758448835371491064747931467840] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 1730).pointIds 1730), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1731).pointIds 1731)]
theorem treeEq7683 : B7683.tree = HexagonCover.NBand.M8300_8500.SplitData.node7683 := by
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

def B7682 : Block := .branch 174 ![288230376151712129, 218424581927470594, 4731607869854765291524, 79228162514264337593543974920, 696898287454081973172991196020261297160208, 393248, 11972621413014756705924586149611790497021949147349056] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B7683]
theorem treeEq7682 : B7682.tree = HexagonCover.NBand.M8300_8500.SplitData.node7682 := by
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
  · exact treeEq7683

def B7681 : Block := .branch 139 ![288230376151712129, 218424581927470594, 4731607869854765291524, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B7682, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1570).pointIds 1570)]
theorem treeEq7681 : B7681.tree = HexagonCover.NBand.M8300_8500.SplitData.node7681 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7682
  · rfl
  · rfl

def B7680 : Block := .branch 147 ![288230376151712129, 218424581927470594, 4731607869854765291524, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7681, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1569).pointIds 1569)]
theorem treeEq7680 : B7680.tree = HexagonCover.NBand.M8300_8500.SplitData.node7680 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7681
  · rfl
  · rfl

def B7679 : Block := .branch 148 ![288230376151712129, 218424581927470594, 4731607869854765291524, 81208866577120946033382549118984, 98320, 393248, 11972621413036540094319509350936938087125823434260544] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7680, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1568).pointIds 1568)]
theorem treeEq7679 : B7679.tree = HexagonCover.NBand.M8300_8500.SplitData.node7679 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7680
  · rfl
  · rfl

def B7678 : Block := .branch 173 ![288230376151712129, 218424581927470594, 4731607869854765291524, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1463).pointIds 1463), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7679]
theorem treeEq7678 : B7678.tree = HexagonCover.NBand.M8300_8500.SplitData.node7678 := by
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
  · exact treeEq7679

def B7677 : Block := .branch 58 ![385, 218565319415825922, 4750090642725493807108, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![B7678, Tip7619_7684, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq7677 : B7677.tree = HexagonCover.NBand.M8300_8500.SplitData.node7677 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7678
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7676 : Block := .branch 56 ![385, 146507725377897986, 4750090642725493807108, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 121).pointIds 121), B7677, Tip7619_7742, (.leaf 3 (Common.fact 123).pointIds 123), (.leaf 4 (Common.fact 124).pointIds 124), (.leaf 5 (Common.fact 125).pointIds 125), (.leaf 6 (Common.fact 126).pointIds 126)]
theorem treeEq7676 : B7676.tree = HexagonCover.NBand.M8300_8500.SplitData.node7676 := by
  change Tree.branch (56 : Fin 177) _ = Tree.branch (56 : Fin 177) _
  apply congrArg (Tree.branch (56 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7677
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7620 : Block := .branch 55 ![385, 146507725377897986, 4750054684297219020804, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 133).pointIds 133), B7621, B7676, (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 137).pointIds 137)]
theorem treeEq7620 : B7620.tree = HexagonCover.NBand.M8300_8500.SplitData.node7620 := by
  change Tree.branch (55 : Fin 177) _ = Tree.branch (55 : Fin 177) _
  apply congrArg (Tree.branch (55 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7621
  · exact treeEq7676
  · rfl
  · rfl
  · rfl
  · rfl

def B7619 : Block := .branch 64 ![385, 146507725377897986, 4731607940223509469188, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 1723).pointIds 1723), B7620, (.leaf 3 (Common.fact 90).pointIds 90), (.leaf 4 (Common.fact 91).pointIds 91), (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 93).pointIds 93)]
theorem treeEq7619 : B7619.tree = HexagonCover.NBand.M8300_8500.SplitData.node7619 := by
  change Tree.branch (64 : Fin 177) _ = Tree.branch (64 : Fin 177) _
  apply congrArg (Tree.branch (64 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7620
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted7619 : B7619.accepted = true := by decide +kernel
theorem checked7619 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7619 (maskNeeds ![385, 146507725377897986, 4731607940223509469188, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq7619]
  exact B7619.sound accepted7619
#print axioms checked7619

def Tip7293_7324 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7324 ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0101.checked7324
def Tip7293_7369 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7369 ![385, 144185556820035074, 4750090642725493807108, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0102.checked7369
def Tip7293_7296 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7296 ![2251799813685633, 144185556820035074, 4750054613928474843140, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738728095214359773890216000] HexagonCover.NBand.M8300_8500.SplitTree.Run0102.checked7296
def B7319 : Block := .branch 79 ![288230376151712129, 144185556820035074, 6148, 24584, 98320, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 1551).pointIds 1551), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1466).pointIds 1466)]
theorem treeEq7319 : B7319.tree = HexagonCover.NBand.M8300_8500.SplitData.node7319 := by
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

def B7318 : Block := .branch 173 ![288230376151712129, 144185556820035074, 4731607869854765291524, 79228162514264337593543974920, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1463).pointIds 1463), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7319]
theorem treeEq7318 : B7318.tree = HexagonCover.NBand.M8300_8500.SplitData.node7318 := by
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
  · exact treeEq7319

def B7323 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7323 : B7323.tree = HexagonCover.NBand.M8300_8500.SplitData.node7323 := by
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

def B7322 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7323, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7322 : B7322.tree = HexagonCover.NBand.M8300_8500.SplitData.node7322 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7323
  · rfl
  · rfl

def B7321 : Block := .branch 173 ![576460752303423873, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1467).pointIds 1467), (.leaf 1 (Common.fact 1537).pointIds 1537), (.leaf 2 (Common.fact 1538).pointIds 1538), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7322]
theorem treeEq7321 : B7321.tree = HexagonCover.NBand.M8300_8500.SplitData.node7321 := by
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
  · exact treeEq7322

def B7320 : Block := .branch 59 ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7321, Tip7293_7324, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7320 : B7320.tree = HexagonCover.NBand.M8300_8500.SplitData.node7320 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7321
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7317 : Block := .branch 58 ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7318, B7320, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq7317 : B7317.tree = HexagonCover.NBand.M8300_8500.SplitData.node7317 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7318
  · exact treeEq7320
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7316 : Block := .branch 55 ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 133).pointIds 133), B7317, Tip7293_7369, (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 137).pointIds 137)]
theorem treeEq7316 : B7316.tree = HexagonCover.NBand.M8300_8500.SplitData.node7316 := by
  change Tree.branch (55 : Fin 177) _ = Tree.branch (55 : Fin 177) _
  apply congrArg (Tree.branch (55 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7317
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7315 : Block := .branch 147 ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7316, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1462).pointIds 1462)]
theorem treeEq7315 : B7315.tree = HexagonCover.NBand.M8300_8500.SplitData.node7315 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7316
  · rfl
  · rfl

def B7314 : Block := .branch 160 ![385, 146437356633720322, 4750054613928474843140, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1549).pointIds 1549), (.leaf 2 (Common.fact 1550).pointIds 1550), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B7315]
theorem treeEq7314 : B7314.tree = HexagonCover.NBand.M8300_8500.SplitData.node7314 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7315

def B7295 : Block := .branch 51 ![385, 144185556820035074, 4750054613928474843140, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![Tip7293_7296, B7314, (.leaf 2 (Common.fact 99).pointIds 99), (.leaf 3 (Common.fact 100).pointIds 100), (.leaf 4 (Common.fact 101).pointIds 101), (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 0 [] 0)]
theorem treeEq7295 : B7295.tree = HexagonCover.NBand.M8300_8500.SplitData.node7295 := by
  change Tree.branch (51 : Fin 177) _ = Tree.branch (51 : Fin 177) _
  apply congrArg (Tree.branch (51 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7314
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7294 : Block := .branch 64 ![385, 144185556820035074, 4731607869854765291524, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 1536).pointIds 1536), B7295, (.leaf 3 (Common.fact 90).pointIds 90), (.leaf 4 (Common.fact 91).pointIds 91), (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 93).pointIds 93)]
theorem treeEq7294 : B7294.tree = HexagonCover.NBand.M8300_8500.SplitData.node7294 := by
  change Tree.branch (64 : Fin 177) _ = Tree.branch (64 : Fin 177) _
  apply congrArg (Tree.branch (64 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7295
  · rfl
  · rfl
  · rfl
  · rfl

def B7293 : Block := .branch 171 ![385, 144185556820035074, 4731607869854765291524, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1008).pointIds 1008), (.leaf 1 (Common.fact 1534).pointIds 1534), (.leaf 2 (Common.fact 1535).pointIds 1535), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), B7294]
theorem treeEq7293 : B7293.tree = HexagonCover.NBand.M8300_8500.SplitData.node7293 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7294

theorem accepted7293 : B7293.accepted = true := by decide +kernel
theorem checked7293 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7293 (maskNeeds ![385, 144185556820035074, 4731607869854765291524, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq7293]
  exact B7293.sound accepted7293
#print axioms checked7293

def Tip0015_7182 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7182 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0099.checked7182
def Tip0015_7227 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7227 ![385, 144115737831671298, 4740849326109117913092, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0100.checked7227
def Tip0015_7155 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7155 ![2251799813685633, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738728095214359773890216000] HexagonCover.NBand.M8300_8500.SplitTree.Run0100.checked7155
def Tip0015_0017 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0017 ![385, 144186106575848962, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0101.checked0017
def B7177 : Block := .branch 79 ![288230376151712129, 144115737831671298, 6148, 24584, 98320, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1466).pointIds 1466)]
theorem treeEq7177 : B7177.tree = HexagonCover.NBand.M8300_8500.SplitData.node7177 := by
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

def B7176 : Block := .branch 173 ![288230376151712129, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1463).pointIds 1463), (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7177]
theorem treeEq7176 : B7176.tree = HexagonCover.NBand.M8300_8500.SplitData.node7176 := by
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
  · exact treeEq7177

def B7181 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7181 : B7181.tree = HexagonCover.NBand.M8300_8500.SplitData.node7181 := by
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

def B7180 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7181, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7180 : B7180.tree = HexagonCover.NBand.M8300_8500.SplitData.node7180 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7181
  · rfl
  · rfl

def B7179 : Block := .branch 173 ![576460752303423873, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1467).pointIds 1467), (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7180]
theorem treeEq7179 : B7179.tree = HexagonCover.NBand.M8300_8500.SplitData.node7179 := by
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
  · exact treeEq7180

def B7178 : Block := .branch 59 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7179, Tip0015_7182, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq7178 : B7178.tree = HexagonCover.NBand.M8300_8500.SplitData.node7178 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7179
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7175 : Block := .branch 58 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7176, B7178, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq7175 : B7175.tree = HexagonCover.NBand.M8300_8500.SplitData.node7175 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7176
  · exact treeEq7178
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7174 : Block := .branch 55 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 133).pointIds 133), B7175, Tip0015_7227, (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 137).pointIds 137)]
theorem treeEq7174 : B7174.tree = HexagonCover.NBand.M8300_8500.SplitData.node7174 := by
  change Tree.branch (55 : Fin 177) _ = Tree.branch (55 : Fin 177) _
  apply congrArg (Tree.branch (55 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7175
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7173 : Block := .branch 147 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7174, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1462).pointIds 1462)]
theorem treeEq7173 : B7173.tree = HexagonCover.NBand.M8300_8500.SplitData.node7173 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7174
  · rfl
  · rfl

def B7172 : Block := .branch 160 ![385, 146367537645356546, 4740813297312098949124, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1528).pointIds 1528), (.leaf 2 (Common.fact 1529).pointIds 1529), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B7173]
theorem treeEq7172 : B7172.tree = HexagonCover.NBand.M8300_8500.SplitData.node7172 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7173

def B7154 : Block := .branch 51 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![Tip0015_7155, B7172, (.leaf 2 (Common.fact 99).pointIds 99), (.leaf 3 (Common.fact 100).pointIds 100), (.leaf 4 (Common.fact 101).pointIds 101), (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 0 [] 0)]
theorem treeEq7154 : B7154.tree = HexagonCover.NBand.M8300_8500.SplitData.node7154 := by
  change Tree.branch (51 : Fin 177) _ = Tree.branch (51 : Fin 177) _
  apply congrArg (Tree.branch (51 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7172
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7153 : Block := .branch 171 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1008).pointIds 1008), (.leaf 1 (Common.fact 1507).pointIds 1507), (.leaf 2 (Common.fact 1508).pointIds 1508), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), B7154]
theorem treeEq7153 : B7153.tree = HexagonCover.NBand.M8300_8500.SplitData.node7153 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7154

def B0016 : Block := .branch 46 ![385, 144115737831671298, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 94).pointIds 94), Tip0015_0017, B7153, (.leaf 3 (Common.fact 95).pointIds 95), (.leaf 4 (Common.fact 96).pointIds 96), (.leaf 5 (Common.fact 97).pointIds 97), (.leaf 6 (Common.fact 98).pointIds 98)]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M8300_8500.SplitData.node0016 := by
  change Tree.branch (46 : Fin 177) _ = Tree.branch (46 : Fin 177) _
  apply congrArg (Tree.branch (46 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7153
  · rfl
  · rfl
  · rfl
  · rfl

def B0015 : Block := .branch 64 ![385, 144115737831671298, 4722366482869645219844, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), B0016, (.leaf 3 (Common.fact 90).pointIds 90), (.leaf 4 (Common.fact 91).pointIds 91), (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 93).pointIds 93)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M8300_8500.SplitData.node0015 := by
  change Tree.branch (64 : Fin 177) _ = Tree.branch (64 : Fin 177) _
  apply congrArg (Tree.branch (64 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0016
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0015 : B0015.accepted = true := by decide +kernel
theorem checked0015 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0015 (maskNeeds ![385, 144115737831671298, 4722366482869645219844, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq0015]
  exact B0015.sound accepted0015
#print axioms checked0015

end HexagonCover.NBand.M8300_8500.SplitTree.Run0107
