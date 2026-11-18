import HexagonCover.N7900.SplitAlignedTree.Run0018
import HexagonCover.N7900.SplitAlignedTree.Run0019
import HexagonCover.N7900.SplitAlignedTree.Run0020
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0021
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip1623_1624 : Block := .tip HexagonCover.N7900.SplitData.node1624 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0020.checked1624
def B1652 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1652 : B1652.tree = HexagonCover.N7900.SplitData.node1652 := by
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

def B1651 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1652]
theorem treeEq1651 : B1651.tree = HexagonCover.N7900.SplitData.node1651 := by
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
  · exact treeEq1652

def B1650 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1651, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1650 : B1650.tree = HexagonCover.N7900.SplitData.node1650 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1651
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1649 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1650, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1649 : B1649.tree = HexagonCover.N7900.SplitData.node1649 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1650
  · rfl
  · rfl

def B1648 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1649, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1648 : B1648.tree = HexagonCover.N7900.SplitData.node1648 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1649
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1647 : Block := .branch 169 ![10394734921872071388083324989735297, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1648, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1647 : B1647.tree = HexagonCover.N7900.SplitData.node1647 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1648
  · rfl

def B1646 : Block := .branch 142 ![10394734921872071388083324989735297, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1647, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1646 : B1646.tree = HexagonCover.N7900.SplitData.node1646 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1647
  · rfl
  · rfl

def B1645 : Block := .branch 88 ![10394734921872071388083324989735297, 302231671076439407461890, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1646]
theorem treeEq1645 : B1645.tree = HexagonCover.N7900.SplitData.node1645 := by
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
  · exact treeEq1646

def B1654 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1654 : B1654.tree = HexagonCover.N7900.SplitData.node1654 := by
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

def B1653 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1654, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1653 : B1653.tree = HexagonCover.N7900.SplitData.node1653 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1654
  · rfl
  · rfl

def B1644 : Block := .branch 78 ![10394734921872071388083324989735297, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1645, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1653]
theorem treeEq1644 : B1644.tree = HexagonCover.N7900.SplitData.node1644 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1645
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1653

def B1661 : Block := .branch 79 ![42545680458834378178474697280335118721, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq1661 : B1661.tree = HexagonCover.N7900.SplitData.node1661 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1660 : Block := .branch 124 ![42545680458834378178474697280335118721, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1661]
theorem treeEq1660 : B1660.tree = HexagonCover.N7900.SplitData.node1660 := by
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
  · exact treeEq1661

def B1659 : Block := .branch 125 ![10384593717070245552871351364092289, 216172782113785346, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1660, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1659 : B1659.tree = HexagonCover.N7900.SplitData.node1659 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1660
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1658 : Block := .branch 157 ![10384593717070245552871351364092289, 216172782113785346, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1659, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1658 : B1658.tree = HexagonCover.N7900.SplitData.node1658 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1659
  · rfl
  · rfl

def B1657 : Block := .branch 166 ![10384593717070245552871351364092289, 216172782113785346, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1658, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1657 : B1657.tree = HexagonCover.N7900.SplitData.node1657 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1658
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1656 : Block := .branch 169 ![10394734921872071388083324989735297, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1657, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1656 : B1656.tree = HexagonCover.N7900.SplitData.node1656 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1657
  · rfl

def B1655 : Block := .branch 143 ![10394734921872071388083324989735297, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1656, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1655 : B1655.tree = HexagonCover.N7900.SplitData.node1655 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1656
  · rfl
  · rfl

def B1643 : Block := .branch 76 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B1644, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1655]
theorem treeEq1643 : B1643.tree = HexagonCover.N7900.SplitData.node1643 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1644
  · rfl
  · rfl
  · rfl
  · exact treeEq1655

def B1623 : Block := .branch 74 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip1623_1624, B1643, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq1623 : B1623.tree = HexagonCover.N7900.SplitData.node1623 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1643
  · rfl
  · rfl
  · rfl

theorem accepted1623 : B1623.accepted = true := by decide +kernel
theorem checked1623 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1623 (maskNeeds ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1623]
  exact B1623.sound accepted1623
#print axioms checked1623

def Tip1662_1663 : Block := .tip HexagonCover.N7900.SplitData.node1663 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0020.checked1663
def B1691 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296461144967597212116121880523902172004416] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1691 : B1691.tree = HexagonCover.N7900.SplitData.node1691 := by
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

def B1690 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1691]
theorem treeEq1690 : B1690.tree = HexagonCover.N7900.SplitData.node1690 := by
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
  · exact treeEq1691

def B1689 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1690, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1689 : B1689.tree = HexagonCover.N7900.SplitData.node1689 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1690
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1688 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1689, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1688 : B1688.tree = HexagonCover.N7900.SplitData.node1688 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1689
  · rfl
  · rfl

def B1687 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1688, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1687 : B1687.tree = HexagonCover.N7900.SplitData.node1687 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1688
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1686 : Block := .branch 169 ![10394734921872071388083324989735297, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1687, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1686 : B1686.tree = HexagonCover.N7900.SplitData.node1686 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1687
  · rfl

def B1685 : Block := .branch 142 ![10394734921872071388083324989735297, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1686, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1685 : B1685.tree = HexagonCover.N7900.SplitData.node1685 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1686
  · rfl
  · rfl

def B1684 : Block := .branch 88 ![10394734921872071388083324989735297, 302231671076439407461890, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1685]
theorem treeEq1684 : B1684.tree = HexagonCover.N7900.SplitData.node1684 := by
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
  · exact treeEq1685

def B1693 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1693 : B1693.tree = HexagonCover.N7900.SplitData.node1693 := by
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

def B1692 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1693, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1692 : B1692.tree = HexagonCover.N7900.SplitData.node1692 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1693
  · rfl
  · rfl

def B1683 : Block := .branch 78 ![10394734921872071388083324989735297, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 599).pointIds 599), B1684, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1692]
theorem treeEq1683 : B1683.tree = HexagonCover.N7900.SplitData.node1683 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1684
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1692

def B1700 : Block := .branch 79 ![42545680458834378178474697280335118721, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296461144967596902706669922904747770642496] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq1700 : B1700.tree = HexagonCover.N7900.SplitData.node1700 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1699 : Block := .branch 124 ![42545680458834378178474697280335118721, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1700]
theorem treeEq1699 : B1699.tree = HexagonCover.N7900.SplitData.node1699 := by
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
  · exact treeEq1700

def B1698 : Block := .branch 125 ![10384593717070245552871351364092289, 216172782113785346, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1699, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1698 : B1698.tree = HexagonCover.N7900.SplitData.node1698 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1699
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1697 : Block := .branch 157 ![10384593717070245552871351364092289, 216172782113785346, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1698, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1697 : B1697.tree = HexagonCover.N7900.SplitData.node1697 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1698
  · rfl
  · rfl

def B1696 : Block := .branch 166 ![10384593717070245552871351364092289, 216172782113785346, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1697, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1696 : B1696.tree = HexagonCover.N7900.SplitData.node1696 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1697
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1695 : Block := .branch 169 ![10394734921872071388083324989735297, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1696, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1695 : B1695.tree = HexagonCover.N7900.SplitData.node1695 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1696
  · rfl

def B1694 : Block := .branch 143 ![10394734921872071388083324989735297, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1695, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1694 : B1694.tree = HexagonCover.N7900.SplitData.node1694 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1695
  · rfl
  · rfl

def B1682 : Block := .branch 76 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B1683, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1694]
theorem treeEq1682 : B1682.tree = HexagonCover.N7900.SplitData.node1682 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1683
  · rfl
  · rfl
  · rfl
  · exact treeEq1694

def B1662 : Block := .branch 74 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip1662_1663, B1682, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq1662 : B1662.tree = HexagonCover.N7900.SplitData.node1662 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1682
  · rfl
  · rfl
  · rfl

theorem accepted1662 : B1662.accepted = true := by decide +kernel
theorem checked1662 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1662 (maskNeeds ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1662]
  exact B1662.sound accepted1662
#print axioms checked1662

def Tip1348_1412 : Block := .tip HexagonCover.N7900.SplitData.node1412 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0018.checked1412
def Tip1348_1350 : Block := .tip HexagonCover.N7900.SplitData.node1350 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0018.checked1350
def Tip1348_1458 : Block := .tip HexagonCover.N7900.SplitData.node1458 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0019.checked1458
def Tip1348_1497 : Block := .tip HexagonCover.N7900.SplitData.node1497 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0019.checked1497
def B1452 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1452 : B1452.tree = HexagonCover.N7900.SplitData.node1452 := by
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

def B1451 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1452, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1451 : B1451.tree = HexagonCover.N7900.SplitData.node1451 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1452
  · rfl
  · rfl

def B1411 : Block := .branch 68 ![10394734921872071388083324989735297, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 659).pointIds 659), Tip1348_1412, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B1451]
theorem treeEq1411 : B1411.tree = HexagonCover.N7900.SplitData.node1411 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1451

def B1410 : Block := .branch 113 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1411, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1410 : B1410.tree = HexagonCover.N7900.SplitData.node1410 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1411
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1409 : Block := .branch 144 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1410, (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1409 : B1409.tree = HexagonCover.N7900.SplitData.node1409 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1410
  · rfl

def B1408 : Block := .branch 161 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38695070960633872881049608, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 694).pointIds 694), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B1409]
theorem treeEq1408 : B1408.tree = HexagonCover.N7900.SplitData.node1408 := by
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
  · exact treeEq1409

def B1349 : Block := .branch 73 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip1348_1350, B1408, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1349 : B1349.tree = HexagonCover.N7900.SplitData.node1349 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1408
  · rfl
  · rfl
  · rfl

def B1457 : Block := .branch 73 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip1348_1458, Tip1348_1497, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1457 : B1457.tree = HexagonCover.N7900.SplitData.node1457 := by
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

def B1537 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1537 : B1537.tree = HexagonCover.N7900.SplitData.node1537 := by
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

def B1536 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1537, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1536 : B1536.tree = HexagonCover.N7900.SplitData.node1536 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1537
  · rfl
  · rfl

def B1456 : Block := .branch 68 ![10394734921872071388083324989735297, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 659).pointIds 659), B1457, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B1536]
theorem treeEq1456 : B1456.tree = HexagonCover.N7900.SplitData.node1456 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1457
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1536

def B1455 : Block := .branch 113 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1456, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1455 : B1455.tree = HexagonCover.N7900.SplitData.node1455 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1456
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1454 : Block := .branch 144 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1455, (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1454 : B1454.tree = HexagonCover.N7900.SplitData.node1454 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1455
  · rfl

def B1453 : Block := .branch 161 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38690348594151003235835912, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 694).pointIds 694), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B1454]
theorem treeEq1453 : B1453.tree = HexagonCover.N7900.SplitData.node1453 := by
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
  · exact treeEq1454

def B1348 : Block := .branch 72 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), B1349, B1453, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq1348 : B1348.tree = HexagonCover.N7900.SplitData.node1348 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1349
  · exact treeEq1453
  · rfl
  · rfl
  · rfl

theorem accepted1348 : B1348.accepted = true := by decide +kernel
theorem checked1348 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1348 (maskNeeds ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1348]
  exact B1348.sound accepted1348
#print axioms checked1348

def Tip1345_1544 : Block := .tip HexagonCover.N7900.SplitData.node1544 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0020.checked1544
def Tip1345_1583 : Block := .tip HexagonCover.N7900.SplitData.node1583 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0020.checked1583
def Tip1345_1623 : Block := .tip HexagonCover.N7900.SplitData.node1623 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1623
def Tip1345_1662 : Block := .tip HexagonCover.N7900.SplitData.node1662 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1662
def Tip1345_1348 : Block := .tip HexagonCover.N7900.SplitData.node1348 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked1348
def B1543 : Block := .branch 73 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip1345_1544, Tip1345_1583, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1543 : B1543.tree = HexagonCover.N7900.SplitData.node1543 := by
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

def B1622 : Block := .branch 73 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip1345_1623, Tip1345_1662, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1622 : B1622.tree = HexagonCover.N7900.SplitData.node1622 := by
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

def B1542 : Block := .branch 72 ![10394734921872071388083324989735297, 442938030551143024130, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), B1543, B1622, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq1542 : B1542.tree = HexagonCover.N7900.SplitData.node1542 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1543
  · exact treeEq1622
  · rfl
  · rfl
  · rfl

def B1702 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1702 : B1702.tree = HexagonCover.N7900.SplitData.node1702 := by
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

def B1701 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1702, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1701 : B1701.tree = HexagonCover.N7900.SplitData.node1701 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1702
  · rfl
  · rfl

def B1541 : Block := .branch 68 ![10394734921872071388083324989735297, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 659).pointIds 659), B1542, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B1701]
theorem treeEq1541 : B1541.tree = HexagonCover.N7900.SplitData.node1541 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1542
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1701

def B1540 : Block := .branch 113 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1541, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1540 : B1540.tree = HexagonCover.N7900.SplitData.node1540 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1541
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1539 : Block := .branch 144 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1540, (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1539 : B1539.tree = HexagonCover.N7900.SplitData.node1539 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1540
  · rfl

def B1538 : Block := .branch 161 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 38687987410909568413229064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 694).pointIds 694), (.leaf 3 (Common.fact 676).pointIds 676), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B1539]
theorem treeEq1538 : B1538.tree = HexagonCover.N7900.SplitData.node1538 := by
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
  · exact treeEq1539

def B1347 : Block := .branch 71 ![10141204802416131022332331295105, 147790125371790198274, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), Tip1345_1348, B1538, (.leaf 4 (Common.fact 322).pointIds 322), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 0 [] 0)]
theorem treeEq1347 : B1347.tree = HexagonCover.N7900.SplitData.node1347 := by
  change Tree.branch (71 : Fin 170) _ = Tree.branch (71 : Fin 170) _
  apply congrArg (Tree.branch (71 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1538
  · rfl
  · rfl
  · rfl

def B1704 : Block := .branch 133 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 164).pointIds 164), (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq1704 : B1704.tree = HexagonCover.N7900.SplitData.node1704 := by
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

def B1703 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B1704, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 506).pointIds 506)]
theorem treeEq1703 : B1703.tree = HexagonCover.N7900.SplitData.node1703 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1704
  · rfl
  · rfl

def B1346 : Block := .branch 69 ![10141204801825835211973625643393, 147790125371790198274, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B1347, (.leaf 1 (Common.fact 423).pointIds 423), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 425).pointIds 425), (.leaf 4 (Common.fact 426).pointIds 426), (.leaf 5 (Common.fact 427).pointIds 427), B1703]
theorem treeEq1346 : B1346.tree = HexagonCover.N7900.SplitData.node1346 := by
  change Tree.branch (69 : Fin 170) _ = Tree.branch (69 : Fin 170) _
  apply congrArg (Tree.branch (69 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1347
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1703

def B1707 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 512).pointIds 512)]
theorem treeEq1707 : B1707.tree = HexagonCover.N7900.SplitData.node1707 := by
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

def B1706 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1707, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 510).pointIds 510)]
theorem treeEq1706 : B1706.tree = HexagonCover.N7900.SplitData.node1706 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1707
  · rfl
  · rfl

def B1705 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1706, (.leaf 6 (Common.fact 509).pointIds 509)]
theorem treeEq1705 : B1705.tree = HexagonCover.N7900.SplitData.node1705 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1706
  · rfl

def B1345 : Block := .branch 67 ![10141204801825835211973625643393, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 106).pointIds 106), B1346, (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B1705]
theorem treeEq1345 : B1345.tree = HexagonCover.N7900.SplitData.node1345 := by
  change Tree.branch (67 : Fin 170) _ = Tree.branch (67 : Fin 170) _
  apply congrArg (Tree.branch (67 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1346
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1705

theorem accepted1345 : B1345.accepted = true := by decide +kernel
theorem checked1345 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1345 (maskNeeds ![10141204801825835211973625643393, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1345]
  exact B1345.sound accepted1345
#print axioms checked1345

end HexagonCover.N7900.SplitAlignedTree.Run0021
