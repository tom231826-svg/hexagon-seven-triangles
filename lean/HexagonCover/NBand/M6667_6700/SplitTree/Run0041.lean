import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0005
import HexagonCover.NBand.M6667_6700.SplitTree.Run0012
import HexagonCover.NBand.M6667_6700.SplitTree.Run0023
import HexagonCover.NBand.M6667_6700.SplitTree.Run0024
import HexagonCover.NBand.M6667_6700.SplitTree.Run0040
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0041
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1715_1729 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1729 ![385, 1297037792194332162, 9007199254747140, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0040.checked1729
def B1726 : Block := .branch 119 ![385, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 374144419156711148358534444761511446371713714487360] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1168).pointIds 1168)]
theorem treeEq1726 : B1726.tree = HexagonCover.NBand.M6667_6700.SplitData.node1726 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1725 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148358534444761511446371713714487360] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1726, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 1167).pointIds 1167)]
theorem treeEq1725 : B1725.tree = HexagonCover.NBand.M6667_6700.SplitData.node1725 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1726
  · rfl
  · rfl

def B1724 : Block := .branch 67 ![385, 1297108160938509826, 9007199254747140, 24584, 98320, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 73).pointIds 73), (.leaf 1 (Common.fact 1162).pointIds 1162), (.leaf 2 (Common.fact 74).pointIds 74), (.leaf 3 (Common.fact 75).pointIds 75), (.leaf 4 (Common.fact 76).pointIds 76), (.leaf 5 (Common.fact 77).pointIds 77), B1725]
theorem treeEq1724 : B1724.tree = HexagonCover.NBand.M6667_6700.SplitData.node1724 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1725

def B1723 : Block := .branch 78 ![385, 1297108160938509826, 9007199254747140, 24584, 98320, 393248, 374144419156711148358534444459132417515466744397888] ![(.leaf 0 (Common.fact 87).pointIds 87), (.leaf 1 (Common.fact 1161).pointIds 1161), (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1724]
theorem treeEq1723 : B1723.tree = HexagonCover.NBand.M6667_6700.SplitData.node1723 := by
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
  · exact treeEq1724

def B1722 : Block := .branch 89 ![385, 1297108160938509826, 9007199254747140, 24584, 98320, 393248, 374144419156711148358534444459132417515466744397888] ![(.leaf 0 (Common.fact 117).pointIds 117), (.leaf 1 (Common.fact 1160).pointIds 1160), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B1723]
theorem treeEq1722 : B1722.tree = HexagonCover.NBand.M6667_6700.SplitData.node1722 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1723

def B2944 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389782551067032915804224] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1222).pointIds 1222)]
theorem treeEq2944 : B2944.tree = HexagonCover.NBand.M6667_6700.SplitData.node2944 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2943 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389782551067032915804224] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2944, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1221).pointIds 1221)]
theorem treeEq2943 : B2943.tree = HexagonCover.NBand.M6667_6700.SplitData.node2943 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2944
  · rfl
  · rfl

def B2942 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 5986310706507378354261318027389782551067032915804224] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2943, (.leaf 6 (Common.fact 1220).pointIds 1220)]
theorem treeEq2942 : B2942.tree = HexagonCover.NBand.M6667_6700.SplitData.node2942 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2943
  · rfl

def B1728 : Block := .branch 63 ![385, 1297037792194332162, 9007199254747140, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 58).pointIds 58), (.leaf 1 (Common.fact 59).pointIds 59), Tip1715_1729, (.leaf 3 (Common.fact 60).pointIds 60), (.leaf 4 (Common.fact 61).pointIds 61), (.leaf 5 (Common.fact 62).pointIds 62), B2942]
theorem treeEq1728 : B1728.tree = HexagonCover.NBand.M6667_6700.SplitData.node1728 := by
  change Tree.branch (63 : Fin 173) _ = Tree.branch (63 : Fin 173) _
  apply congrArg (Tree.branch (63 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2942

def B2947 : Block := .branch 119 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389777939381014488416320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 699).pointIds 699), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1225).pointIds 1225)]
theorem treeEq2947 : B2947.tree = HexagonCover.NBand.M6667_6700.SplitData.node2947 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2946 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389777939381014488416320] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2947, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1224).pointIds 1224)]
theorem treeEq2946 : B2946.tree = HexagonCover.NBand.M6667_6700.SplitData.node2946 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2947
  · rfl
  · rfl

def B2945 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 5986310706507378354261318027389777939381014488416320] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2946, (.leaf 6 (Common.fact 1223).pointIds 1223)]
theorem treeEq2945 : B2945.tree = HexagonCover.NBand.M6667_6700.SplitData.node2945 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2946
  · rfl

def B1727 : Block := .branch 62 ![385, 1297037792194332162, 9007199254747140, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 53).pointIds 53), (.leaf 1 (Common.fact 54).pointIds 54), B1728, (.leaf 3 (Common.fact 55).pointIds 55), (.leaf 4 (Common.fact 56).pointIds 56), (.leaf 5 (Common.fact 57).pointIds 57), B2945]
theorem treeEq1727 : B1727.tree = HexagonCover.NBand.M6667_6700.SplitData.node1727 := by
  change Tree.branch (62 : Fin 173) _ = Tree.branch (62 : Fin 173) _
  apply congrArg (Tree.branch (62 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1728
  · rfl
  · rfl
  · rfl
  · exact treeEq2945

def B1721 : Block := .branch 46 ![385, 1297037792194332162, 9007199254747140, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 1155).pointIds 1155), B1722, B1727, (.leaf 3 (Common.fact 1156).pointIds 1156), (.leaf 4 (Common.fact 1157).pointIds 1157), (.leaf 5 (Common.fact 1158).pointIds 1158), (.leaf 6 (Common.fact 1159).pointIds 1159)]
theorem treeEq1721 : B1721.tree = HexagonCover.NBand.M6667_6700.SplitData.node1721 := by
  change Tree.branch (46 : Fin 173) _ = Tree.branch (46 : Fin 173) _
  apply congrArg (Tree.branch (46 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1722
  · exact treeEq1727
  · rfl
  · rfl
  · rfl
  · rfl

def B1720 : Block := .branch 105 ![385, 1297037792194332162, 9007199254747140, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 845).pointIds 845), (.leaf 1 (Common.fact 846).pointIds 846), (.leaf 2 (Common.fact 847).pointIds 847), B1721, (.leaf 4 (Common.fact 848).pointIds 848), (.leaf 5 (Common.fact 849).pointIds 849), (.leaf 6 (Common.fact 1154).pointIds 1154)]
theorem treeEq1720 : B1720.tree = HexagonCover.NBand.M6667_6700.SplitData.node1720 := by
  change Tree.branch (105 : Fin 173) _ = Tree.branch (105 : Fin 173) _
  apply congrArg (Tree.branch (105 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1721
  · rfl
  · rfl
  · rfl

def B1719 : Block := .branch 148 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B1720, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 994).pointIds 994)]
theorem treeEq1719 : B1719.tree = HexagonCover.NBand.M6667_6700.SplitData.node1719 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1720
  · rfl
  · rfl

def B1718 : Block := .branch 172 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 1150).pointIds 1150), (.leaf 1 (Common.fact 1151).pointIds 1151), (.leaf 2 (Common.fact 1152).pointIds 1152), (.leaf 3 (Common.fact 1153).pointIds 1153), (.leaf 4 (Common.fact 993).pointIds 993), (.leaf 5 (Common.fact 896).pointIds 896), B1719]
theorem treeEq1718 : B1718.tree = HexagonCover.NBand.M6667_6700.SplitData.node1718 := by
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
  · exact treeEq1719

def B1717 : Block := .branch 92 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![B1718, (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 835).pointIds 835), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 988).pointIds 988)]
theorem treeEq1717 : B1717.tree = HexagonCover.NBand.M6667_6700.SplitData.node1717 := by
  change Tree.branch (92 : Fin 173) _ = Tree.branch (92 : Fin 173) _
  apply congrArg (Tree.branch (92 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1718
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1716 : Block := .branch 134 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B1717, (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq1716 : B1716.tree = HexagonCover.NBand.M6667_6700.SplitData.node1716 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1717
  · rfl

def B1715 : Block := .branch 143 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B1716, (.leaf 6 (Common.fact 986).pointIds 986)]
theorem treeEq1715 : B1715.tree = HexagonCover.NBand.M6667_6700.SplitData.node1715 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1716
  · rfl

theorem accepted1715 : B1715.accepted = true := by decide +kernel
theorem checked1715 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1715 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632]) := by
  rw [← treeEq1715]
  exact B1715.sound accepted1715
#print axioms checked1715

def Tip0009_0384 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0384 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 98320, 393248, 1298708368761643957013057709277248] HexagonCover.NBand.M6667_6700.SplitTree.Run0005.checked0384
def Tip0009_0021 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0021 ![1208926972536133781553537, 302231454904756805305858, 77919046967349146032132, 19342813113834066795323400, 98320, 393248, 1299025416811392811201899452170304] HexagonCover.NBand.M6667_6700.SplitTree.Run0005.checked0021
def Tip0009_0406 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0406 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 24584, 98320, 393248, 1298391283235194694770711550492736] HexagonCover.NBand.M6667_6700.SplitTree.Run0005.checked0406
def Tip0009_0425 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0425 ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 24584, 98320, 393248, 1298391282328500330059739669463104] HexagonCover.NBand.M6667_6700.SplitTree.Run0005.checked0425
def Tip0009_0444 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0444 ![1152921504606847361, 147573953689188042242, 2416523473655951267844, 24584, 98320, 393248, 1299024952659435942910210688417856] HexagonCover.NBand.M6667_6700.SplitTree.Run0012.checked0444
def Tip0009_0900 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0900 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 1299025262068887900529365089779776] HexagonCover.NBand.M6667_6700.SplitTree.Run0023.checked0900
def Tip0009_1646 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1646 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025107326530563809420403802176] HexagonCover.NBand.M6667_6700.SplitTree.Run0023.checked1646
def Tip0009_1662 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1662 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 98320, 393248, 1299024952583914972672443784101952] HexagonCover.NBand.M6667_6700.SplitTree.Run0023.checked1662
def Tip0009_1677 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1677 ![385, 1538, 6148, 24584, 98320, 393248, 1299025262068906347273438799331392] HexagonCover.NBand.M6667_6700.SplitTree.Run0023.checked1677
def Tip0009_1692 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1692 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025262068897123901401944555584] HexagonCover.NBand.M6667_6700.SplitTree.Run0024.checked1692
def Tip0009_1715 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1715 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] checked1715
def B0383 : Block := .branch 143 ![1152921504606847361, 302231454904756805305858, 77919046967349146032132, 9671406556917033397673992, 98320, 393248, 1298708368761643957013057709277248] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), Tip0009_0384, (.leaf 6 (Common.fact 768).pointIds 768)]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M6667_6700.SplitData.node0383 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0020 : Block := .branch 84 ![1208926972536133781553537, 302231454904756805305858, 77937493711422855583748, 9671406556917033397673992, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), Tip0009_0021, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B0383]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M6667_6700.SplitData.node0020 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0383

def B0405 : Block := .branch 122 ![11692013098647223345629478661731417078752067191169, 1538, 6148, 24584, 98320, 393248, 1298708359090237400096024311627840] ![(.leaf 0 (Common.fact 806).pointIds 806), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0405 : B0405.tree = HexagonCover.NBand.M6667_6700.SplitData.node0405 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0404 : Block := .branch 163 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1298708359090237400096024311627840] ![B0405, (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 805).pointIds 805)]
theorem treeEq0404 : B0404.tree = HexagonCover.NBand.M6667_6700.SplitData.node0404 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0405
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0019 : Block := .branch 83 ![1208926972536133781553537, 302231454904756805305858, 77937493711422855583748, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 99).pointIds 99), B0020, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), B0404]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M6667_6700.SplitData.node0019 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl
  · exact treeEq0404

def B0018 : Block := .branch 80 ![1152921504606847361, 302231454904756805305858, 77937493711422855583748, 24584, 98320, 393248, 1299025416811392811201899452170304] ![B0019, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), Tip0009_0406]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M6667_6700.SplitData.node0018 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0019
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0017 : Block := .branch 78 ![1152921504606847361, 147573953689188042242, 77937493711422855583748, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 87).pointIds 87), B0018, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip0009_0425]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M6667_6700.SplitData.node0017 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0018
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0016 : Block := .branch 76 ![1152921504606847361, 147573953689188042242, 2416523473655951267844, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), B0017, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), Tip0009_0444]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M6667_6700.SplitData.node0016 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0017
  · rfl
  · rfl
  · rfl
  · rfl

def B0015 : Block := .branch 71 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 78).pointIds 78), (.leaf 1 (Common.fact 79).pointIds 79), B0016, Tip0009_0900, (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), (.leaf 0 [] 0)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M6667_6700.SplitData.node0015 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0016
  · rfl
  · rfl
  · rfl
  · rfl

def B0014 : Block := .branch 67 ![1152921504606847361, 1099511629314, 55340232221128660996, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 73).pointIds 73), B0015, (.leaf 2 (Common.fact 74).pointIds 74), (.leaf 3 (Common.fact 75).pointIds 75), (.leaf 4 (Common.fact 76).pointIds 76), (.leaf 5 (Common.fact 77).pointIds 77), Tip0009_1646]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M6667_6700.SplitData.node0014 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0015
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0013 : Block := .branch 65 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 68).pointIds 68), (.leaf 1 (Common.fact 69).pointIds 69), B0014, (.leaf 3 (Common.fact 70).pointIds 70), (.leaf 4 (Common.fact 71).pointIds 71), (.leaf 5 (Common.fact 72).pointIds 72), Tip0009_1662]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M6667_6700.SplitData.node0013 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0014
  · rfl
  · rfl
  · rfl
  · rfl

def B0012 : Block := .branch 64 ![1152921504606847361, 144116287587485186, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 63).pointIds 63), (.leaf 1 (Common.fact 64).pointIds 64), B0013, (.leaf 3 (Common.fact 65).pointIds 65), (.leaf 4 (Common.fact 66).pointIds 66), (.leaf 5 (Common.fact 67).pointIds 67), Tip0009_1677]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M6667_6700.SplitData.node0012 := by
  change Tree.branch (64 : Fin 173) _ = Tree.branch (64 : Fin 173) _
  apply congrArg (Tree.branch (64 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0013
  · rfl
  · rfl
  · rfl
  · rfl

def B0011 : Block := .branch 63 ![1152921504606847361, 144116287587485186, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 58).pointIds 58), (.leaf 1 (Common.fact 59).pointIds 59), B0012, (.leaf 3 (Common.fact 60).pointIds 60), (.leaf 4 (Common.fact 61).pointIds 61), (.leaf 5 (Common.fact 62).pointIds 62), Tip0009_1692]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M6667_6700.SplitData.node0011 := by
  change Tree.branch (63 : Fin 173) _ = Tree.branch (63 : Fin 173) _
  apply congrArg (Tree.branch (63 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0012
  · rfl
  · rfl
  · rfl
  · rfl

def B1712 : Block := .branch 122 ![11692013098647223345629478661731417078752067191169, 1538, 6148, 24584, 98320, 393248, 1299025262068892512215383517167680] ![(.leaf 0 (Common.fact 806).pointIds 806), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 1145).pointIds 1145)]
theorem treeEq1712 : B1712.tree = HexagonCover.NBand.M6667_6700.SplitData.node1712 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1711 : Block := .branch 163 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025262068892512215383517167680] ![B1712, (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 1144).pointIds 1144)]
theorem treeEq1711 : B1711.tree = HexagonCover.NBand.M6667_6700.SplitData.node1711 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1712
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0010 : Block := .branch 62 ![1152921504606847361, 144116287587485186, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 53).pointIds 53), (.leaf 1 (Common.fact 54).pointIds 54), B0011, (.leaf 3 (Common.fact 55).pointIds 55), (.leaf 4 (Common.fact 56).pointIds 56), (.leaf 5 (Common.fact 57).pointIds 57), B1711]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M6667_6700.SplitData.node0010 := by
  change Tree.branch (62 : Fin 173) _ = Tree.branch (62 : Fin 173) _
  apply congrArg (Tree.branch (62 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl
  · exact treeEq1711

def B1714 : Block := .branch 147 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 980).pointIds 980), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 982).pointIds 982), (.leaf 3 (Common.fact 983).pointIds 983), Tip0009_1715, (.leaf 5 (Common.fact 984).pointIds 984), (.leaf 6 (Common.fact 985).pointIds 985)]
theorem treeEq1714 : B1714.tree = HexagonCover.NBand.M6667_6700.SplitData.node1714 := by
  change Tree.branch (147 : Fin 173) _ = Tree.branch (147 : Fin 173) _
  apply congrArg (Tree.branch (147 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1713 : Block := .branch 168 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 1299025262068887900529365089779776] ![(.leaf 0 (Common.fact 1146).pointIds 1146), (.leaf 1 (Common.fact 1147).pointIds 1147), (.leaf 2 (Common.fact 1148).pointIds 1148), (.leaf 3 (Common.fact 1149).pointIds 1149), (.leaf 4 (Common.fact 389).pointIds 389), (.leaf 5 (Common.fact 318).pointIds 318), B1714]
theorem treeEq1713 : B1713.tree = HexagonCover.NBand.M6667_6700.SplitData.node1713 := by
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
  · exact treeEq1714

def B0009 : Block := .branch 60 ![385, 144116287587485186, 9007199254747140, 24584, 98320, 393248, 1299025416811392811201899452170304] ![B0010, B1713, (.leaf 2 (Common.fact 49).pointIds 49), (.leaf 3 (Common.fact 50).pointIds 50), (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 0 [] 0)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M6667_6700.SplitData.node0009 := by
  change Tree.branch (60 : Fin 173) _ = Tree.branch (60 : Fin 173) _
  apply congrArg (Tree.branch (60 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0010
  · exact treeEq1713
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0009 : B0009.accepted = true := by decide +kernel
theorem checked0009 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0009 (maskNeeds ![385, 144116287587485186, 9007199254747140, 24584, 98320, 393248, 1299025416811392811201899452170304]) := by
  rw [← treeEq0009]
  exact B0009.sound accepted0009
#print axioms checked0009

def Tip0007_0009 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0009 ![385, 144116287587485186, 9007199254747140, 24584, 98320, 393248, 1299025416811392811201899452170304] checked0009
def B2961 : Block := .branch 129 ![385, 1538, 6148, 24584, 4878288012178573812210938372141829079531536, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 1238).pointIds 1238), (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 1239).pointIds 1239)]
theorem treeEq2961 : B2961.tree = HexagonCover.NBand.M6667_6700.SplitData.node2961 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2960 : Block := .branch 141 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), B2961, (.leaf 5 (Common.fact 184).pointIds 184), (.leaf 6 (Common.fact 1237).pointIds 1237)]
theorem treeEq2960 : B2960.tree = HexagonCover.NBand.M6667_6700.SplitData.node2960 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2961
  · rfl
  · rfl

def B2959 : Block := .branch 62 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 2659755016677158128941586139363934272] ![(.leaf 0 (Common.fact 53).pointIds 53), (.leaf 1 (Common.fact 54).pointIds 54), B2960, (.leaf 3 (Common.fact 55).pointIds 55), (.leaf 4 (Common.fact 56).pointIds 56), (.leaf 5 (Common.fact 57).pointIds 57), (.leaf 6 (Common.fact 1236).pointIds 1236)]
theorem treeEq2959 : B2959.tree = HexagonCover.NBand.M6667_6700.SplitData.node2959 := by
  change Tree.branch (62 : Fin 173) _ = Tree.branch (62 : Fin 173) _
  apply congrArg (Tree.branch (62 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2960
  · rfl
  · rfl
  · rfl
  · rfl

def B2958 : Block := .branch 91 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 2659755016677158128941586139363934272] ![B2959, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 1235).pointIds 1235)]
theorem treeEq2958 : B2958.tree = HexagonCover.NBand.M6667_6700.SplitData.node2958 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2959
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2957 : Block := .branch 121 ![385, 1538, 6148, 24584, 715714541215342186448661958312808352082657296, 10889035741470030830827987437816583159840, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 430).pointIds 430), B2958]
theorem treeEq2957 : B2957.tree = HexagonCover.NBand.M6667_6700.SplitData.node2957 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2958

def B2956 : Block := .branch 149 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B2957, (.leaf 5 (Common.fact 208).pointIds 208), (.leaf 6 (Common.fact 1234).pointIds 1234)]
theorem treeEq2956 : B2956.tree = HexagonCover.NBand.M6667_6700.SplitData.node2956 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2957
  · rfl
  · rfl

def B2955 : Block := .branch 133 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B2956, (.leaf 6 (Common.fact 1233).pointIds 1233)]
theorem treeEq2955 : B2955.tree = HexagonCover.NBand.M6667_6700.SplitData.node2955 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2956
  · rfl

def B2954 : Block := .branch 134 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B2955, (.leaf 6 (Common.fact 1232).pointIds 1232)]
theorem treeEq2954 : B2954.tree = HexagonCover.NBand.M6667_6700.SplitData.node2954 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2955
  · rfl

def B2953 : Block := .branch 139 ![385, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B2954, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1231).pointIds 1231)]
theorem treeEq2953 : B2953.tree = HexagonCover.NBand.M6667_6700.SplitData.node2953 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2954
  · rfl
  · rfl

def B2952 : Block := .branch 106 ![385, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 1058).pointIds 1058), (.leaf 1 (Common.fact 1059).pointIds 1059), (.leaf 2 (Common.fact 1060).pointIds 1060), B2953, (.leaf 4 (Common.fact 1061).pointIds 1061), (.leaf 5 (Common.fact 1062).pointIds 1062), (.leaf 6 (Common.fact 1230).pointIds 1230)]
theorem treeEq2952 : B2952.tree = HexagonCover.NBand.M6667_6700.SplitData.node2952 := by
  change Tree.branch (106 : Fin 173) _ = Tree.branch (106 : Fin 173) _
  apply congrArg (Tree.branch (106 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2953
  · rfl
  · rfl
  · rfl

def B2951 : Block := .branch 117 ![385, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 778).pointIds 778), (.leaf 2 (Common.fact 779).pointIds 779), B2952, (.leaf 4 (Common.fact 1056).pointIds 1056), (.leaf 5 (Common.fact 781).pointIds 781), (.leaf 6 (Common.fact 1229).pointIds 1229)]
theorem treeEq2951 : B2951.tree = HexagonCover.NBand.M6667_6700.SplitData.node2951 := by
  change Tree.branch (117 : Fin 173) _ = Tree.branch (117 : Fin 173) _
  apply congrArg (Tree.branch (117 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2952
  · rfl
  · rfl
  · rfl

def B2950 : Block := .branch 140 ![385, 1538, 6148, 24584, 98320, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2951, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1228).pointIds 1228)]
theorem treeEq2950 : B2950.tree = HexagonCover.NBand.M6667_6700.SplitData.node2950 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2951
  · rfl
  · rfl

def B2949 : Block := .branch 143 ![385, 1538, 6148, 24584, 98320, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B2950, (.leaf 6 (Common.fact 1227).pointIds 1227)]
theorem treeEq2949 : B2949.tree = HexagonCover.NBand.M6667_6700.SplitData.node2949 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2950
  · rfl

def B2948 : Block := .branch 148 ![385, 1538, 6148, 24584, 98320, 393248, 1299025107326383133972018803245120] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B2949, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 1226).pointIds 1226)]
theorem treeEq2948 : B2948.tree = HexagonCover.NBand.M6667_6700.SplitData.node2948 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2949
  · rfl
  · rfl

def B0008 : Block := .branch 57 ![385, 1099511629314, 9007199254747140, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 44).pointIds 44), Tip0007_0009, (.leaf 2 (Common.fact 45).pointIds 45), (.leaf 3 (Common.fact 46).pointIds 46), (.leaf 4 (Common.fact 47).pointIds 47), (.leaf 5 (Common.fact 48).pointIds 48), B2948]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M6667_6700.SplitData.node0008 := by
  change Tree.branch (57 : Fin 173) _ = Tree.branch (57 : Fin 173) _
  apply congrArg (Tree.branch (57 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2948

def B2963 : Block := .branch 122 ![11692013098647223345629478661730264157247460344193, 1538, 6148, 24584, 98320, 393248, 1299025262068887909536564344520768] ![(.leaf 0 (Common.fact 1241).pointIds 1241), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 1242).pointIds 1242)]
theorem treeEq2963 : B2963.tree = HexagonCover.NBand.M6667_6700.SplitData.node2963 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2962 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1299025262068887909536564344520768] ![B2963, (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 1240).pointIds 1240)]
theorem treeEq2962 : B2962.tree = HexagonCover.NBand.M6667_6700.SplitData.node2962 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2963
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 53 ![385, 1099511629314, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 39).pointIds 39), (.leaf 1 (Common.fact 40).pointIds 40), B0008, (.leaf 3 (Common.fact 41).pointIds 41), (.leaf 4 (Common.fact 42).pointIds 42), (.leaf 5 (Common.fact 43).pointIds 43), B2962]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M6667_6700.SplitData.node0007 := by
  change Tree.branch (53 : Fin 173) _ = Tree.branch (53 : Fin 173) _
  apply congrArg (Tree.branch (53 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0008
  · rfl
  · rfl
  · rfl
  · exact treeEq2962

theorem accepted0007 : B0007.accepted = true := by decide +kernel
theorem checked0007 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0007 (maskNeeds ![385, 1099511629314, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304]) := by
  rw [← treeEq0007]
  exact B0007.sound accepted0007
#print axioms checked0007

def B3026 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3026 : B3026.tree = HexagonCover.NBand.M6667_6700.SplitData.node3026 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3025 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3026]
theorem treeEq3025 : B3025.tree = HexagonCover.NBand.M6667_6700.SplitData.node3025 := by
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
  · exact treeEq3026

def B3028 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq3028 : B3028.tree = HexagonCover.NBand.M6667_6700.SplitData.node3028 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3027 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3028, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3027 : B3027.tree = HexagonCover.NBand.M6667_6700.SplitData.node3027 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3028
  · rfl
  · rfl

def B3024 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3025, (.leaf 5 (Common.fact 439).pointIds 439), B3027]
theorem treeEq3024 : B3024.tree = HexagonCover.NBand.M6667_6700.SplitData.node3024 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3025
  · rfl
  · exact treeEq3027

def B3030 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3030 : B3030.tree = HexagonCover.NBand.M6667_6700.SplitData.node3030 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3029 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3030]
theorem treeEq3029 : B3029.tree = HexagonCover.NBand.M6667_6700.SplitData.node3029 := by
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
  · exact treeEq3030

def B3023 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715684808496787692392546368] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3024, B3029, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3023 : B3023.tree = HexagonCover.NBand.M6667_6700.SplitData.node3023 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3024
  · exact treeEq3029
  · rfl
  · rfl

def B3033 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233346055704656513842282560] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3033 : B3033.tree = HexagonCover.NBand.M6667_6700.SplitData.node3033 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3032 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699695943108080401163994267712] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3033]
theorem treeEq3032 : B3032.tree = HexagonCover.NBand.M6667_6700.SplitData.node3032 := by
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
  · exact treeEq3033

def B3031 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724991292464235241714316944097148992] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3032, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3031 : B3031.tree = HexagonCover.NBand.M6667_6700.SplitData.node3031 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3032
  · rfl
  · rfl

def B3022 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3023, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3031, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3022 : B3022.tree = HexagonCover.NBand.M6667_6700.SplitData.node3022 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3023
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3031
  · rfl

def B3036 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3036 : B3036.tree = HexagonCover.NBand.M6667_6700.SplitData.node3036 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3035 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3036]
theorem treeEq3035 : B3035.tree = HexagonCover.NBand.M6667_6700.SplitData.node3035 := by
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
  · exact treeEq3036

def B3034 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3035, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3034 : B3034.tree = HexagonCover.NBand.M6667_6700.SplitData.node3034 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3035
  · rfl
  · rfl

def B3021 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3022, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3034]
theorem treeEq3021 : B3021.tree = HexagonCover.NBand.M6667_6700.SplitData.node3021 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3022
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3034

def B3020 : Block := .branch 140 ![385, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3021, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq3020 : B3020.tree = HexagonCover.NBand.M6667_6700.SplitData.node3020 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3021
  · rfl
  · rfl

def B3019 : Block := .branch 163 ![5319508131568930906582414993892835713, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B3020]
theorem treeEq3019 : B3019.tree = HexagonCover.NBand.M6667_6700.SplitData.node3019 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3020

theorem accepted3019 : B3019.accepted = true := by decide +kernel
theorem checked3019 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3019 (maskNeeds ![5319508131568930906582414993892835713, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968]) := by
  rw [← treeEq3019]
  exact B3019.sound accepted3019
#print axioms checked3019

end HexagonCover.NBand.M6667_6700.SplitTree.Run0041
