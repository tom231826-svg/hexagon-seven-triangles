import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0013
import HexagonCover.NBand.M6900_7100.SplitTree.Run0014
import HexagonCover.NBand.M6900_7100.SplitTree.Run0020
import HexagonCover.NBand.M6900_7100.SplitTree.Run0021
import HexagonCover.NBand.M6900_7100.SplitTree.Run0024
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0028
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1635_1805 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1805 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0024.checked1805
def Tip1635_1753 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1753 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0024.checked1753
def Tip1635_1636 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1636 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0024.checked1636
def B1881 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq1881 : B1881.tree = HexagonCover.NBand.M6900_7100.SplitData.node1881 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1880 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1881, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1880 : B1880.tree = HexagonCover.NBand.M6900_7100.SplitData.node1880 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1881
  · rfl
  · rfl

def B1879 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1880]
theorem treeEq1879 : B1879.tree = HexagonCover.NBand.M6900_7100.SplitData.node1879 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1880

def B1878 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438917017082873731800891456] ![B1879, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1878 : B1878.tree = HexagonCover.NBand.M6900_7100.SplitData.node1878 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1879
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1877 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1878, (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq1877 : B1877.tree = HexagonCover.NBand.M6900_7100.SplitData.node1877 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1878
  · rfl

def B1876 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756092385535905650531893312] ![B1877, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1876 : B1876.tree = HexagonCover.NBand.M6900_7100.SplitData.node1876 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1877
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1875 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1876, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1875 : B1875.tree = HexagonCover.NBand.M6900_7100.SplitData.node1875 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1876
  · rfl

def B1874 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1875, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq1874 : B1874.tree = HexagonCover.NBand.M6900_7100.SplitData.node1874 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1875
  · rfl
  · rfl

def B1804 : Block := .branch 78 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip1635_1805, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1874]
theorem treeEq1804 : B1804.tree = HexagonCover.NBand.M6900_7100.SplitData.node1804 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1874

def B1752 : Block := .branch 69 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip1635_1753, B1804, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq1752 : B1752.tree = HexagonCover.NBand.M6900_7100.SplitData.node1752 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1804
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1751 : Block := .branch 91 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B1752, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq1751 : B1751.tree = HexagonCover.NBand.M6900_7100.SplitData.node1751 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1752
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1635 : Block := .branch 76 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip1635_1636, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B1751]
theorem treeEq1635 : B1635.tree = HexagonCover.NBand.M6900_7100.SplitData.node1635 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1751

theorem accepted1635 : B1635.accepted = true := by decide +kernel
theorem checked1635 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1635 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1635]
  exact B1635.sound accepted1635
#print axioms checked1635

def Tip1139_1557 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1557 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0020.checked1557
def Tip1139_1505 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1505 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0020.checked1505
def Tip1139_1388 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1388 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0021.checked1388
def Tip1139_1140 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1140 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0021.checked1140
def B1633 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq1633 : B1633.tree = HexagonCover.NBand.M6900_7100.SplitData.node1633 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1632 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1633, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1632 : B1632.tree = HexagonCover.NBand.M6900_7100.SplitData.node1632 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1633
  · rfl
  · rfl

def B1631 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1632]
theorem treeEq1631 : B1631.tree = HexagonCover.NBand.M6900_7100.SplitData.node1631 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1632

def B1630 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438917017082873731800891456] ![B1631, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1630 : B1630.tree = HexagonCover.NBand.M6900_7100.SplitData.node1630 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1631
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1629 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1630, (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq1629 : B1629.tree = HexagonCover.NBand.M6900_7100.SplitData.node1629 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1630
  · rfl

def B1628 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756092385535905650531893312] ![B1629, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1628 : B1628.tree = HexagonCover.NBand.M6900_7100.SplitData.node1628 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1629
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1627 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1628, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1627 : B1627.tree = HexagonCover.NBand.M6900_7100.SplitData.node1627 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1628
  · rfl

def B1626 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1627, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq1626 : B1626.tree = HexagonCover.NBand.M6900_7100.SplitData.node1626 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1627
  · rfl
  · rfl

def B1556 : Block := .branch 78 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip1139_1557, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1626]
theorem treeEq1556 : B1556.tree = HexagonCover.NBand.M6900_7100.SplitData.node1556 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1626

def B1504 : Block := .branch 69 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip1139_1505, B1556, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq1504 : B1504.tree = HexagonCover.NBand.M6900_7100.SplitData.node1504 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1556
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1503 : Block := .branch 91 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B1504, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq1503 : B1503.tree = HexagonCover.NBand.M6900_7100.SplitData.node1503 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1504
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1387 : Block := .branch 76 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip1139_1388, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B1503]
theorem treeEq1387 : B1387.tree = HexagonCover.NBand.M6900_7100.SplitData.node1387 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1503

def B1139 : Block := .branch 74 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), Tip1139_1140, B1387, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq1139 : B1139.tree = HexagonCover.NBand.M6900_7100.SplitData.node1139 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1387
  · rfl
  · rfl
  · rfl

theorem accepted1139 : B1139.accepted = true := by decide +kernel
theorem checked1139 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1139 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1139]
  exact B1139.sound accepted1139
#print axioms checked1139

def Tip0122_1061 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1061 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0013.checked1061
def Tip0122_1009 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1009 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0013.checked1009
def Tip0122_0892 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0892 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0014.checked0892
def Tip0122_0644 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0644 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0014.checked0644
def Tip0122_0123 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0123 ![10384593717069655257060992658440577, 443658607591033931266, 11861292468192260659204, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0014.checked0123
def B1137 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq1137 : B1137.tree = HexagonCover.NBand.M6900_7100.SplitData.node1137 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1136 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 98320, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B1137, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1136 : B1136.tree = HexagonCover.NBand.M6900_7100.SplitData.node1136 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1137
  · rfl
  · rfl

def B1135 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1136]
theorem treeEq1135 : B1135.tree = HexagonCover.NBand.M6900_7100.SplitData.node1135 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1136

def B1134 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438917017082873731800891456] ![B1135, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1134 : B1134.tree = HexagonCover.NBand.M6900_7100.SplitData.node1134 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1135
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1133 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1134, (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq1133 : B1133.tree = HexagonCover.NBand.M6900_7100.SplitData.node1133 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1134
  · rfl

def B1132 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756092385535905650531893312] ![B1133, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1132 : B1132.tree = HexagonCover.NBand.M6900_7100.SplitData.node1132 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1133
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1131 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1132, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1131 : B1131.tree = HexagonCover.NBand.M6900_7100.SplitData.node1131 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1132
  · rfl

def B1130 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1131, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq1130 : B1130.tree = HexagonCover.NBand.M6900_7100.SplitData.node1130 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1131
  · rfl
  · rfl

def B1060 : Block := .branch 78 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip0122_1061, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1130]
theorem treeEq1060 : B1060.tree = HexagonCover.NBand.M6900_7100.SplitData.node1060 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1130

def B1008 : Block := .branch 69 ![10384596192949733827821542456689025, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip0122_1009, B1060, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq1008 : B1008.tree = HexagonCover.NBand.M6900_7100.SplitData.node1008 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1060
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1007 : Block := .branch 91 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B1008, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq1007 : B1007.tree = HexagonCover.NBand.M6900_7100.SplitData.node1007 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1008
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0891 : Block := .branch 76 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip0122_0892, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B1007]
theorem treeEq0891 : B0891.tree = HexagonCover.NBand.M6900_7100.SplitData.node0891 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1007

def B0643 : Block := .branch 74 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), Tip0122_0644, B0891, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq0643 : B0643.tree = HexagonCover.NBand.M6900_7100.SplitData.node0643 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0891
  · rfl
  · rfl
  · rfl

def B0122 : Block := .branch 73 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), Tip0122_0123, B0643, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M6900_7100.SplitData.node0122 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0643
  · rfl
  · rfl
  · rfl

theorem accepted0122 : B0122.accepted = true := by decide +kernel
theorem checked0122 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0122 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0122]
  exact B0122.sound accepted0122
#print axioms checked0122

def B2164 : Block := .branch 171 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 790).pointIds 790), (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq2164 : B2164.tree = HexagonCover.NBand.M6900_7100.SplitData.node2164 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2165 : Block := .branch 171 ![93536104789177791958600338428897971189972715176321, 2192252455996354377305527249074424530583410443778, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 793).pointIds 793), (.leaf 1 (Common.fact 794).pointIds 794), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 790).pointIds 790), (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq2165 : B2165.tree = HexagonCover.NBand.M6900_7100.SplitData.node2165 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2166 : Block := .branch 171 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2854495427947215627233879871820816201736912928, 730767566023689488259195761341071153223765065792] ![(.leaf 0 (Common.fact 793).pointIds 793), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 790).pointIds 790), (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 795).pointIds 795)]
theorem treeEq2166 : B2166.tree = HexagonCover.NBand.M6900_7100.SplitData.node2166 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2163 : Block := .branch 159 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![B2164, B2165, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B2166]
theorem treeEq2163 : B2163.tree = HexagonCover.NBand.M6900_7100.SplitData.node2163 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2164
  · exact treeEq2165
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2166

def B2167 : Block := .branch 171 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17720707352637197883219678596684931613328182181904, 46770906890016840598145148526792877445191578288160, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 793).pointIds 793), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 796).pointIds 796), (.leaf 5 (Common.fact 797).pointIds 797), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq2167 : B2167.tree = HexagonCover.NBand.M6900_7100.SplitData.node2167 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2162 : Block := .branch 165 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17720707352637197883219678596684931613328182181904, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), B2163, B2167, (.leaf 0 [] 0)]
theorem treeEq2162 : B2162.tree = HexagonCover.NBand.M6900_7100.SplitData.node2162 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2163
  · exact treeEq2167
  · rfl

def B2168 : Block := .branch 171 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 185542200094310080402694483961356193658728480800, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 793).pointIds 793), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 798).pointIds 798), (.leaf 5 (Common.fact 799).pointIds 799), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq2168 : B2168.tree = HexagonCover.NBand.M6900_7100.SplitData.node2168 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2161 : Block := .branch 157 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2162, B2168, (.leaf 0 [] 0)]
theorem treeEq2161 : B2161.tree = HexagonCover.NBand.M6900_7100.SplitData.node2161 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2162
  · exact treeEq2168
  · rfl

def B2160 : Block := .branch 166 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 2854495427947215627233879871820816201736912928, 16747358238029157353344982929643395798794304] ![B2161, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq2160 : B2160.tree = HexagonCover.NBand.M6900_7100.SplitData.node2160 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2161
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2174 : Block := .branch 172 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2993155353253731711777011654710880546081278819434528, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 803).pointIds 803), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 807).pointIds 807), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq2174 : B2174.tree = HexagonCover.NBand.M6900_7100.SplitData.node2174 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2175 : Block := .branch 172 ![93536104789177791958600338428897971189972715176321, 2192252455996354377305527249074424530583410443778, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2993155353253731711777011654710880546081278819434528, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 810).pointIds 810), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 807).pointIds 807), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq2175 : B2175.tree = HexagonCover.NBand.M6900_7100.SplitData.node2175 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2176 : Block := .branch 172 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2993155353253731711777011654710880546081278819434528, 733605335850202510053956181491265657225401073728] ![(.leaf 0 (Common.fact 810).pointIds 810), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 807).pointIds 807), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq2176 : B2176.tree = HexagonCover.NBand.M6900_7100.SplitData.node2176 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2173 : Block := .branch 159 ![93536104789177791958600338428897971189972715176321, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2993155353253731711777011654710880546081278819434528, 2854517184751050952113765133124147397434802240] ![B2174, B2175, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B2176]
theorem treeEq2173 : B2173.tree = HexagonCover.NBand.M6900_7100.SplitData.node2173 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2174
  · exact treeEq2175
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2176

def B2177 : Block := .branch 172 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 93536104789177786765035829293842113257979683143712, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 813).pointIds 813), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 807).pointIds 807), (.leaf 5 (Common.fact 814).pointIds 814), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq2177 : B2177.tree = HexagonCover.NBand.M6900_7100.SplitData.node2177 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2172 : Block := .branch 166 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 52796746648578867920108114581875724085070563213328, 2993155353253731711777011654710880546081278819434528, 2860092371050683607899149062692309487811297344] ![B2173, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), B2177, (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq2172 : B2172.tree = HexagonCover.NBand.M6900_7100.SplitData.node2172 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2173
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2177
  · rfl

def B2178 : Block := .branch 172 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17720707352637197883219678596684931613328182181904, 3039923405648320605159529569357801602710268660809760, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 813).pointIds 813), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 815).pointIds 815), (.leaf 5 (Common.fact 816).pointIds 816), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq2178 : B2178.tree = HexagonCover.NBand.M6900_7100.SplitData.node2178 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2171 : Block := .branch 165 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17720707352637197883219678596684931613328182181904, 2993155353253731711777011654710880546081278819434528, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), B2172, B2178, (.leaf 0 [] 0)]
theorem treeEq2171 : B2171.tree = HexagonCover.NBand.M6900_7100.SplitData.node2171 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2172
  · exact treeEq2178
  · rfl

def B2170 : Block := .branch 157 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17538019647970835018444217992595396235871190614032, 2993155353253731711777011654710880546081278819434528, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2171, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2170 : B2170.tree = HexagonCover.NBand.M6900_7100.SplitData.node2170 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2171
  · rfl
  · rfl

def B2169 : Block := .branch 171 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 2860092371050683607899149062692309487811297344] ![(.leaf 0 (Common.fact 800).pointIds 800), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 798).pointIds 798), B2170, (.leaf 6 (Common.fact 801).pointIds 801)]
theorem treeEq2169 : B2169.tree = HexagonCover.NBand.M6900_7100.SplitData.node2169 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2170
  · rfl

def B2159 : Block := .branch 151 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663541302843829936991572514163593936912, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B2160, B2169]
theorem treeEq2159 : B2159.tree = HexagonCover.NBand.M6900_7100.SplitData.node2159 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2160
  · exact treeEq2169

theorem accepted2159 : B2159.accepted = true := by decide +kernel
theorem checked2159 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2159 (maskNeeds ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663541302843829936991572514163593936912, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304]) := by
  rw [← treeEq2159]
  exact B2159.sound accepted2159
#print axioms checked2159

def Tip2149_2159 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2159 ![5193564509135055857931993032425857, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663541302843829936991572514163593936912, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] checked2159
def B2179 : Block := .branch 172 ![1267650600228229401496703205761, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747358243221454211879810558173892128014400] ![(.leaf 0 (Common.fact 817).pointIds 817), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 818).pointIds 818), (.leaf 5 (Common.fact 819).pointIds 819), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq2179 : B2179.tree = HexagonCover.NBand.M6900_7100.SplitData.node2179 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2158 : Block := .branch 112 ![1267650600228229401496703205761, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663541302843829936991572514163593936912, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![Tip2149_2159, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B2179]
theorem treeEq2158 : B2158.tree = HexagonCover.NBand.M6900_7100.SplitData.node2158 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2179

def B2180 : Block := .branch 172 ![2536539140495744183268305535361, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747358238030425003945211159044892501999680] ![(.leaf 0 (Common.fact 821).pointIds 821), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 818).pointIds 818), (.leaf 5 (Common.fact 819).pointIds 819), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq2180 : B2180.tree = HexagonCover.NBand.M6900_7100.SplitData.node2180 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2157 : Block := .branch 100 ![2536539140495744183268305535361, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663541302843829936991572514163593936912, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![B2158, (.leaf 1 (Common.fact 784).pointIds 784), (.leaf 2 (Common.fact 539).pointIds 539), (.leaf 3 (Common.fact 540).pointIds 540), (.leaf 4 (Common.fact 541).pointIds 541), (.leaf 5 (Common.fact 542).pointIds 542), B2180]
theorem treeEq2157 : B2157.tree = HexagonCover.NBand.M6900_7100.SplitData.node2157 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2158
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2180

def B2181 : Block := .branch 172 ![748288838313422294122821936155656274674145455767937, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663540978325276278564845731007573360656, 42535295865117307932921825928971419680, 16747358238029158281800012393678601973137472] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 804).pointIds 804), (.leaf 2 (Common.fact 805).pointIds 805), (.leaf 3 (Common.fact 806).pointIds 806), (.leaf 4 (Common.fact 818).pointIds 818), (.leaf 5 (Common.fact 819).pointIds 819), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq2181 : B2181.tree = HexagonCover.NBand.M6900_7100.SplitData.node2181 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2156 : Block := .branch 90 ![748288838313422294122821936155656274674145455767937, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 17539446895663541302843829936991572514163593936912, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![B2157, (.leaf 1 (Common.fact 783).pointIds 783), (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), B2181]
theorem treeEq2156 : B2156.tree = HexagonCover.NBand.M6900_7100.SplitData.node2156 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2157
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2181

def B2155 : Block := .branch 162 ![748288838313422294122821936155656274674145455767937, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 174224571863520570666861437582767328092168, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 781).pointIds 781), B2156, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq2155 : B2155.tree = HexagonCover.NBand.M6900_7100.SplitData.node2155 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2156
  · rfl
  · rfl

def B2154 : Block := .branch 137 ![748288838313422294122821936155656274674145455767937, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 77373613638577702003826696, 11693440346339929630029090606126440435539863765008, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B2155, (.leaf 4 (Common.fact 780).pointIds 780), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq2154 : B2154.tree = HexagonCover.NBand.M6900_7100.SplitData.node2154 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2155
  · rfl
  · rfl
  · rfl

def B2153 : Block := .branch 163 ![748288838313422294122821936155656274674145455767937, 1461501637330902918204303802735925710892893734402, 374144419156711147060143317255648683240702699640836, 77373613638577702003826696, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2154, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq2153 : B2153.tree = HexagonCover.NBand.M6900_7100.SplitData.node2153 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2154
  · rfl
  · rfl

def B2152 : Block := .branch 160 ![748288838313422294122821936155656274674145455767937, 618970019642691236961191426, 374144419156711147060143317255648683240702699640836, 77373613638577702003826696, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 299).pointIds 299), B2153, (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 778).pointIds 778)]
theorem treeEq2152 : B2152.tree = HexagonCover.NBand.M6900_7100.SplitData.node2152 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2153
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2151 : Block := .branch 168 ![748288838313422294122821936155656274674145455767937, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 16747358238029157353344982929643395798794304] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), B2152, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq2151 : B2151.tree = HexagonCover.NBand.M6900_7100.SplitData.node2151 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2152
  · rfl
  · rfl
  · rfl
  · rfl

def B2150 : Block := .branch 124 ![748288838313422294122821936155656274674145455767937, 618970020002979207150831106, 80280230208783968638980, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 775).pointIds 775), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B2151]
theorem treeEq2150 : B2150.tree = HexagonCover.NBand.M6900_7100.SplitData.node2150 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2151

def B2185 : Block := .branch 124 ![730750818665451459101842416358141509827966271873, 1538, 6148, 24584, 98320, 393248, 374144435904048117441368111866384921762350044282944] ![(.leaf 0 (Common.fact 827).pointIds 827), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq2185 : B2185.tree = HexagonCover.NBand.M6900_7100.SplitData.node2185 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2184 : Block := .branch 159 ![385, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144435904048117441368111866384921762350044282944] ![B2185, (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq2184 : B2184.tree = HexagonCover.NBand.M6900_7100.SplitData.node2184 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2185
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2183 : Block := .branch 168 ![385, 619574482912786521738184194, 4384504911992708754611054502871215541837442848772, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 392).pointIds 392), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2184]
theorem treeEq2183 : B2183.tree = HexagonCover.NBand.M6900_7100.SplitData.node2183 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2184

def B2182 : Block := .branch 160 ![385, 619574482912786521738184194, 2923003274661805836407369670154932522181510305796, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 16747336970381224794691016468730431313281088] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 578).pointIds 578), B2183, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 778).pointIds 778)]
theorem treeEq2182 : B2182.tree = HexagonCover.NBand.M6900_7100.SplitData.node2182 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2183
  · rfl
  · rfl
  · rfl
  · rfl

def B2149 : Block := .branch 79 ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 2923003274661805836407369745712796248095833724932, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088] ![B2150, B2182, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 774).pointIds 774)]
theorem treeEq2149 : B2149.tree = HexagonCover.NBand.M6900_7100.SplitData.node2149 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2150
  · exact treeEq2182
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2149 : B2149.accepted = true := by decide +kernel
theorem checked2149 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2149 (maskNeeds ![748288838313422294122821935551193364866830868414849, 618970020002979207150831106, 2923003274661805836407369745712796248095833724932, 116059239866245835594424328, 2140871539059264340141087380901025860594794512, 42535295865117307932921825928971419680, 16747336970381224794691016468730431313281088]) := by
  rw [← treeEq2149]
  exact B2149.sound accepted2149
#print axioms checked2149

end HexagonCover.NBand.M6900_7100.SplitTree.Run0028
