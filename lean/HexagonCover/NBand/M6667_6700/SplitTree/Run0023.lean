import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0022
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0023
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0900_1200 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1200 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] HexagonCover.NBand.M6667_6700.SplitTree.Run0022.checked1200
def Tip0900_1634 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1634 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] HexagonCover.NBand.M6667_6700.SplitTree.Run0022.checked1634
def Tip0900_0909 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0909 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0022.checked0909
def B1630 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261001134158087247904603003945024] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq1630 : B1630.tree = HexagonCover.NBand.M6667_6700.SplitData.node1630 := by
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

def B1629 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1630, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1629 : B1629.tree = HexagonCover.NBand.M6667_6700.SplitData.node1629 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1630
  · rfl
  · rfl

def B1628 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1629, (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq1628 : B1628.tree = HexagonCover.NBand.M6667_6700.SplitData.node1628 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1629
  · rfl

def B1199 : Block := .branch 84 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), Tip0900_1200, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B1628]
theorem treeEq1199 : B1199.tree = HexagonCover.NBand.M6667_6700.SplitData.node1199 := by
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
  · exact treeEq1628

def B1633 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq1633 : B1633.tree = HexagonCover.NBand.M6667_6700.SplitData.node1633 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1632 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1633, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1632 : B1632.tree = HexagonCover.NBand.M6667_6700.SplitData.node1632 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1633
  · rfl
  · rfl

def B1631 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1632, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq1631 : B1631.tree = HexagonCover.NBand.M6667_6700.SplitData.node1631 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1632
  · rfl

def B1198 : Block := .branch 80 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![B1199, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B1631]
theorem treeEq1198 : B1198.tree = HexagonCover.NBand.M6667_6700.SplitData.node1198 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1199
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1631

def B1197 : Block := .branch 78 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 87).pointIds 87), B1198, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip0900_1634]
theorem treeEq1197 : B1197.tree = HexagonCover.NBand.M6667_6700.SplitData.node1197 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1198
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0908 : Block := .branch 76 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), Tip0900_0909, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), B1197]
theorem treeEq0908 : B0908.tree = HexagonCover.NBand.M6667_6700.SplitData.node0908 := by
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
  · exact treeEq1197

def B0907 : Block := .branch 148 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0908, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 994).pointIds 994)]
theorem treeEq0907 : B0907.tree = HexagonCover.NBand.M6667_6700.SplitData.node0907 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0908
  · rfl
  · rfl

def B0906 : Block := .branch 172 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 990).pointIds 990), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 991).pointIds 991), (.leaf 3 (Common.fact 992).pointIds 992), (.leaf 4 (Common.fact 993).pointIds 993), (.leaf 5 (Common.fact 896).pointIds 896), B0907]
theorem treeEq0906 : B0906.tree = HexagonCover.NBand.M6667_6700.SplitData.node0906 := by
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
  · exact treeEq0907

def B0905 : Block := .branch 83 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 99).pointIds 99), B0906, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), (.leaf 6 (Common.fact 989).pointIds 989)]
theorem treeEq0905 : B0905.tree = HexagonCover.NBand.M6667_6700.SplitData.node0905 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0906
  · rfl
  · rfl
  · rfl

def B0904 : Block := .branch 92 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![B0905, (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 835).pointIds 835), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 988).pointIds 988)]
theorem treeEq0904 : B0904.tree = HexagonCover.NBand.M6667_6700.SplitData.node0904 := by
  change Tree.branch (92 : Fin 173) _ = Tree.branch (92 : Fin 173) _
  apply congrArg (Tree.branch (92 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0905
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0903 : Block := .branch 134 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0904, (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq0903 : B0903.tree = HexagonCover.NBand.M6667_6700.SplitData.node0903 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0904
  · rfl

def B0902 : Block := .branch 143 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0903, (.leaf 6 (Common.fact 986).pointIds 986)]
theorem treeEq0902 : B0902.tree = HexagonCover.NBand.M6667_6700.SplitData.node0902 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0903
  · rfl

def B0901 : Block := .branch 147 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 980).pointIds 980), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 982).pointIds 982), (.leaf 3 (Common.fact 983).pointIds 983), B0902, (.leaf 5 (Common.fact 984).pointIds 984), (.leaf 6 (Common.fact 985).pointIds 985)]
theorem treeEq0901 : B0901.tree = HexagonCover.NBand.M6667_6700.SplitData.node0901 := by
  change Tree.branch (147 : Fin 173) _ = Tree.branch (147 : Fin 173) _
  apply congrArg (Tree.branch (147 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0902
  · rfl
  · rfl

def B0900 : Block := .branch 168 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 1299025262068887900529365089779776] ![(.leaf 0 (Common.fact 977).pointIds 977), (.leaf 1 (Common.fact 860).pointIds 860), (.leaf 2 (Common.fact 978).pointIds 978), (.leaf 3 (Common.fact 979).pointIds 979), (.leaf 4 (Common.fact 389).pointIds 389), (.leaf 5 (Common.fact 318).pointIds 318), B0901]
theorem treeEq0900 : B0900.tree = HexagonCover.NBand.M6667_6700.SplitData.node0900 := by
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
  · exact treeEq0901

theorem accepted0900 : B0900.accepted = true := by decide +kernel
theorem checked0900 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0900 (maskNeeds ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 98320, 393248, 1299025262068887900529365089779776]) := by
  rw [← treeEq0900]
  exact B0900.sound accepted0900
#print axioms checked0900

def B1661 : Block := .branch 119 ![385, 1538, 6148, 24584, 3402823669209384634633746074317682212880, 393248, 10889035741787098223537529413864552661056] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 1082).pointIds 1082), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1083).pointIds 1083)]
theorem treeEq1661 : B1661.tree = HexagonCover.NBand.M6667_6700.SplitData.node1661 := by
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

def B1660 : Block := .branch 131 ![385, 1538, 6148, 24584, 680564733841876926926749214863536521232, 393248, 10889035741787098223537529413864552661056] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), B1661, (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1081).pointIds 1081)]
theorem treeEq1660 : B1660.tree = HexagonCover.NBand.M6667_6700.SplitData.node1660 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1661
  · rfl
  · rfl

def B1659 : Block := .branch 59 ![46768052394588893382517914646922209550494448222593, 1538, 6148, 24584, 680564733841876926926749214863536521232, 393248, 10889035741787098223537529413864552661056] ![(.leaf 0 (Common.fact 1075).pointIds 1075), B1660, (.leaf 2 (Common.fact 1076).pointIds 1076), (.leaf 3 (Common.fact 1077).pointIds 1077), (.leaf 4 (Common.fact 1078).pointIds 1078), (.leaf 5 (Common.fact 1079).pointIds 1079), (.leaf 6 (Common.fact 1080).pointIds 1080)]
theorem treeEq1659 : B1659.tree = HexagonCover.NBand.M6667_6700.SplitData.node1659 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1660
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1658 : Block := .branch 165 ![1152921504606847361, 1538, 6148, 24584, 680564733841876926926749214863536521232, 2787593149816327892691964784081045188640800, 10889035741787098223537529413864552661056] ![B1659, (.leaf 1 (Common.fact 440).pointIds 440), (.leaf 2 (Common.fact 441).pointIds 441), (.leaf 3 (Common.fact 442).pointIds 442), (.leaf 4 (Common.fact 443).pointIds 443), (.leaf 5 (Common.fact 1073).pointIds 1073), (.leaf 6 (Common.fact 1074).pointIds 1074)]
theorem treeEq1658 : B1658.tree = HexagonCover.NBand.M6667_6700.SplitData.node1658 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1659
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1657 : Block := .branch 133 ![1152921504606847361, 1538, 6148, 24584, 680564733841876926926749214863536521232, 2787593149816327892691964784081045188640800, 317067392709541976047969894464] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 184).pointIds 184), B1658]
theorem treeEq1657 : B1657.tree = HexagonCover.NBand.M6667_6700.SplitData.node1657 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1658

def B1656 : Block := .branch 141 ![1152921504606847361, 1538, 6148, 24584, 1394477139642005823272909141255386130645008, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1071).pointIds 1071), B1657, (.leaf 6 (Common.fact 1072).pointIds 1072)]
theorem treeEq1656 : B1656.tree = HexagonCover.NBand.M6667_6700.SplitData.node1656 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1657
  · rfl

def B1655 : Block := .branch 142 ![1152921504606847361, 1538, 6148, 24584, 1394477139642005823272909141255386130645008, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 1069).pointIds 1069), B1656, (.leaf 6 (Common.fact 1070).pointIds 1070)]
theorem treeEq1655 : B1655.tree = HexagonCover.NBand.M6667_6700.SplitData.node1655 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1656
  · rfl

def B1654 : Block := .branch 150 ![1152921504606847361, 1538, 6148, 24584, 1394477139642005823272909141255386130645008, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 1067).pointIds 1067), B1655, (.leaf 6 (Common.fact 1068).pointIds 1068)]
theorem treeEq1654 : B1654.tree = HexagonCover.NBand.M6667_6700.SplitData.node1654 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1655
  · rfl

def B1653 : Block := .branch 129 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B1654, (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 1066).pointIds 1066)]
theorem treeEq1653 : B1653.tree = HexagonCover.NBand.M6667_6700.SplitData.node1653 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1654
  · rfl
  · rfl

def B1652 : Block := .branch 134 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B1653, (.leaf 6 (Common.fact 1065).pointIds 1065)]
theorem treeEq1652 : B1652.tree = HexagonCover.NBand.M6667_6700.SplitData.node1652 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1653
  · rfl

def B1651 : Block := .branch 139 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B1652, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq1651 : B1651.tree = HexagonCover.NBand.M6667_6700.SplitData.node1651 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1652
  · rfl
  · rfl

def B1650 : Block := .branch 106 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 1058).pointIds 1058), (.leaf 1 (Common.fact 1059).pointIds 1059), (.leaf 2 (Common.fact 1060).pointIds 1060), B1651, (.leaf 4 (Common.fact 1061).pointIds 1061), (.leaf 5 (Common.fact 1062).pointIds 1062), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq1650 : B1650.tree = HexagonCover.NBand.M6667_6700.SplitData.node1650 := by
  change Tree.branch (106 : Fin 173) _ = Tree.branch (106 : Fin 173) _
  apply congrArg (Tree.branch (106 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1651
  · rfl
  · rfl
  · rfl

def B1649 : Block := .branch 117 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 778).pointIds 778), (.leaf 2 (Common.fact 779).pointIds 779), B1650, (.leaf 4 (Common.fact 1056).pointIds 1056), (.leaf 5 (Common.fact 781).pointIds 781), (.leaf 6 (Common.fact 1057).pointIds 1057)]
theorem treeEq1649 : B1649.tree = HexagonCover.NBand.M6667_6700.SplitData.node1649 := by
  change Tree.branch (117 : Fin 173) _ = Tree.branch (117 : Fin 173) _
  apply congrArg (Tree.branch (117 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1650
  · rfl
  · rfl
  · rfl

def B1648 : Block := .branch 140 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1649, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1055).pointIds 1055)]
theorem treeEq1648 : B1648.tree = HexagonCover.NBand.M6667_6700.SplitData.node1648 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1649
  · rfl
  · rfl

def B1647 : Block := .branch 143 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B1648, (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq1647 : B1647.tree = HexagonCover.NBand.M6667_6700.SplitData.node1647 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1648
  · rfl

def B1646 : Block := .branch 148 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025107326530563809420403802176] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B1647, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 1053).pointIds 1053)]
theorem treeEq1646 : B1646.tree = HexagonCover.NBand.M6667_6700.SplitData.node1646 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1647
  · rfl
  · rfl

theorem accepted1646 : B1646.accepted = true := by decide +kernel
theorem checked1646 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1646 (maskNeeds ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025107326530563809420403802176]) := by
  rw [← treeEq1646]
  exact B1646.sound accepted1646
#print axioms checked1646

def B1676 : Block := .branch 172 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 9671406556917033397673992, 2090694862362245919518973588060783891283984, 21778071482940061661655974875633165926432, 2999001359803012789452669316667670671656043186487360] ![(.leaf 0 (Common.fact 891).pointIds 891), (.leaf 1 (Common.fact 1099).pointIds 1099), (.leaf 2 (Common.fact 1100).pointIds 1100), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 1101).pointIds 1101), (.leaf 5 (Common.fact 631).pointIds 631), (.leaf 6 (Common.fact 1102).pointIds 1102)]
theorem treeEq1676 : B1676.tree = HexagonCover.NBand.M6667_6700.SplitData.node1676 := by
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

def B1675 : Block := .branch 171 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 29014219670751100192972808, 748288840404117156482532553869710494124621353287696, 21778071482940061661655974875633165926432, 5846006549323612971522779264723047400693338472512] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 1097).pointIds 1097), (.leaf 2 (Common.fact 1098).pointIds 1098), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 541).pointIds 541), B1676]
theorem treeEq1675 : B1675.tree = HexagonCover.NBand.M6667_6700.SplitData.node1675 := by
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
  · exact treeEq1676

def B1674 : Block := .branch 84 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 9671406556917033397673992, 748288840404117156482532553869710494124621353287696, 21778071482940061661655974875633165926432, 5846006549323612971839691914780104751067514273856] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B1675, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq1674 : B1674.tree = HexagonCover.NBand.M6667_6700.SplitData.node1674 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1675
  · rfl
  · rfl
  · rfl

def B1673 : Block := .branch 95 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 9671406556917033397673992, 748288840404117156482532553869710494124621353287696, 21778071482940061661655974875633165926432, 5846006549323612971839691914780104751067514273856] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), B1674, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq1673 : B1673.tree = HexagonCover.NBand.M6667_6700.SplitData.node1673 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1674
  · rfl
  · rfl
  · rfl

def B1672 : Block := .branch 162 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 9671406556917033397673992, 748288840404117156482532553869710494124621353287696, 21778071482940061661655974875633165926432, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 1094).pointIds 1094), (.leaf 5 (Common.fact 227).pointIds 227), B1673]
theorem treeEq1672 : B1672.tree = HexagonCover.NBand.M6667_6700.SplitData.node1672 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1673

def B1671 : Block := .branch 164 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 9671406556917033397673992, 748288840404117156482532553869710494124621353287696, 21778071482940061661655974875633165926432, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 545).pointIds 545), B1672, (.leaf 0 [] 0)]
theorem treeEq1671 : B1671.tree = HexagonCover.NBand.M6667_6700.SplitData.node1671 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1672
  · rfl

def B1670 : Block := .branch 166 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 9671406556917033397673992, 748288840404117156482532553869710494124621353287696, 21778071482940061661655974875633165926432, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 544).pointIds 544), B1671, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq1670 : B1670.tree = HexagonCover.NBand.M6667_6700.SplitData.node1670 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1671
  · rfl

def B1669 : Block := .branch 169 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 9671406556917033397673992, 2090694862362245919518973588060783891283984, 21778071482940061661655974875633165926432, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 1091).pointIds 1091), (.leaf 2 (Common.fact 1092).pointIds 1092), (.leaf 3 (Common.fact 900).pointIds 900), B1670, (.leaf 5 (Common.fact 752).pointIds 752), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq1669 : B1669.tree = HexagonCover.NBand.M6667_6700.SplitData.node1669 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1670
  · rfl
  · rfl

def B1668 : Block := .branch 83 ![4951760158294442604203344257, 144116287587485186, 18446744073709557764, 24584, 2090694862362245919518973588060783891283984, 21778071482940061661655974875633165926432, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 99).pointIds 99), B1669, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq1668 : B1668.tree = HexagonCover.NBand.M6667_6700.SplitData.node1668 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1669
  · rfl
  · rfl
  · rfl

def B1667 : Block := .branch 92 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 2090694862362245919518973588060783891283984, 21778071482940061661655974875633165926432, 1299024952583914972672443784101952] ![B1668, (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 835).pointIds 835), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 1089).pointIds 1089)]
theorem treeEq1667 : B1667.tree = HexagonCover.NBand.M6667_6700.SplitData.node1667 := by
  change Tree.branch (92 : Fin 173) _ = Tree.branch (92 : Fin 173) _
  apply congrArg (Tree.branch (92 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1668
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1666 : Block := .branch 134 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 2090694862362245919518973588060783891283984, 393248, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B1667, (.leaf 6 (Common.fact 1088).pointIds 1088)]
theorem treeEq1666 : B1666.tree = HexagonCover.NBand.M6667_6700.SplitData.node1666 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1667
  · rfl

def B1665 : Block := .branch 139 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 1393796574908163946345982392040522594222096, 393248, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B1666, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1087).pointIds 1087)]
theorem treeEq1665 : B1665.tree = HexagonCover.NBand.M6667_6700.SplitData.node1665 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1666
  · rfl
  · rfl

def B1664 : Block := .branch 140 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 98320, 393248, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1665, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1086).pointIds 1086)]
theorem treeEq1664 : B1664.tree = HexagonCover.NBand.M6667_6700.SplitData.node1664 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1665
  · rfl
  · rfl

def B1663 : Block := .branch 143 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 98320, 393248, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B1664, (.leaf 6 (Common.fact 1085).pointIds 1085)]
theorem treeEq1663 : B1663.tree = HexagonCover.NBand.M6667_6700.SplitData.node1663 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1664
  · rfl

def B1662 : Block := .branch 148 ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 98320, 393248, 1299024952583914972672443784101952] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B1663, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 1084).pointIds 1084)]
theorem treeEq1662 : B1662.tree = HexagonCover.NBand.M6667_6700.SplitData.node1662 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1663
  · rfl
  · rfl

theorem accepted1662 : B1662.accepted = true := by decide +kernel
theorem checked1662 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1662 (maskNeeds ![1152921504606847361, 144116287587485186, 18446744073709557764, 24584, 98320, 393248, 1299024952583914972672443784101952]) := by
  rw [← treeEq1662]
  exact B1662.sound accepted1662
#print axioms checked1662

def B1691 : Block := .branch 132 ![385, 1538, 6148, 24584, 2790315408751695400399671780940499334037520, 393248, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 1117).pointIds 1117), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1118).pointIds 1118)]
theorem treeEq1691 : B1691.tree = HexagonCover.NBand.M6667_6700.SplitData.node1691 := by
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

def B1690 : Block := .branch 131 ![385, 1538, 6148, 24584, 2787593149816327892691964784081045188345872, 393248, 5846006549326271427831571231517286966183090192448] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), B1691, (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1116).pointIds 1116)]
theorem treeEq1690 : B1690.tree = HexagonCover.NBand.M6667_6700.SplitData.node1690 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1691
  · rfl
  · rfl

def B1689 : Block := .branch 162 ![385, 1538, 6148, 24584, 4878288012178573812210938372141829079531536, 393248, 2659755016831900652154887559360020544] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 1115).pointIds 1115), (.leaf 5 (Common.fact 227).pointIds 227), B1690]
theorem treeEq1689 : B1689.tree = HexagonCover.NBand.M6667_6700.SplitData.node1689 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1690

def B1688 : Block := .branch 164 ![385, 1538, 6148, 24584, 4878288012178573812210938372141829079531536, 393248, 2659755016831900652154887559360020544] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 1114).pointIds 1114), B1689, (.leaf 0 [] 0)]
theorem treeEq1688 : B1688.tree = HexagonCover.NBand.M6667_6700.SplitData.node1688 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1689
  · rfl

def B1687 : Block := .branch 166 ![385, 1538, 6148, 24584, 4878288012178573812210938372141829079531536, 393248, 2659755016831900652154887559360020544] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 1113).pointIds 1113), B1688, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq1687 : B1687.tree = HexagonCover.NBand.M6667_6700.SplitData.node1687 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1688
  · rfl

def B1686 : Block := .branch 141 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 2659755016831900652154887559360020544] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), B1687, (.leaf 5 (Common.fact 184).pointIds 184), (.leaf 6 (Common.fact 1112).pointIds 1112)]
theorem treeEq1686 : B1686.tree = HexagonCover.NBand.M6667_6700.SplitData.node1686 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1687
  · rfl
  · rfl

def B1685 : Block := .branch 105 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 2659755016831900652154887559360020544] ![(.leaf 0 (Common.fact 845).pointIds 845), (.leaf 1 (Common.fact 846).pointIds 846), (.leaf 2 (Common.fact 847).pointIds 847), B1686, (.leaf 4 (Common.fact 848).pointIds 848), (.leaf 5 (Common.fact 849).pointIds 849), (.leaf 6 (Common.fact 1111).pointIds 1111)]
theorem treeEq1685 : B1685.tree = HexagonCover.NBand.M6667_6700.SplitData.node1685 := by
  change Tree.branch (105 : Fin 173) _ = Tree.branch (105 : Fin 173) _
  apply congrArg (Tree.branch (105 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1686
  · rfl
  · rfl
  · rfl

def B1684 : Block := .branch 121 ![385, 1538, 6148, 24584, 715714541215342186448661958312808352082657296, 10889035741470030830827987437816583159840, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 430).pointIds 430), B1685]
theorem treeEq1684 : B1684.tree = HexagonCover.NBand.M6667_6700.SplitData.node1684 := by
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
  · exact treeEq1685

def B1683 : Block := .branch 149 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B1684, (.leaf 5 (Common.fact 208).pointIds 208), (.leaf 6 (Common.fact 1109).pointIds 1109)]
theorem treeEq1683 : B1683.tree = HexagonCover.NBand.M6667_6700.SplitData.node1683 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1684
  · rfl
  · rfl

def B1682 : Block := .branch 133 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 393248, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B1683, (.leaf 6 (Common.fact 1108).pointIds 1108)]
theorem treeEq1682 : B1682.tree = HexagonCover.NBand.M6667_6700.SplitData.node1682 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1683
  · rfl

def B1681 : Block := .branch 134 ![385, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 393248, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B1682, (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq1681 : B1681.tree = HexagonCover.NBand.M6667_6700.SplitData.node1681 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1682
  · rfl

def B1680 : Block := .branch 139 ![385, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B1681, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1106).pointIds 1106)]
theorem treeEq1680 : B1680.tree = HexagonCover.NBand.M6667_6700.SplitData.node1680 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1681
  · rfl
  · rfl

def B1679 : Block := .branch 140 ![385, 1538, 6148, 24584, 98320, 393248, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1680, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq1679 : B1679.tree = HexagonCover.NBand.M6667_6700.SplitData.node1679 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1680
  · rfl
  · rfl

def B1678 : Block := .branch 143 ![385, 1538, 6148, 24584, 98320, 393248, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B1679, (.leaf 6 (Common.fact 1104).pointIds 1104)]
theorem treeEq1678 : B1678.tree = HexagonCover.NBand.M6667_6700.SplitData.node1678 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1679
  · rfl

def B1677 : Block := .branch 148 ![385, 1538, 6148, 24584, 98320, 393248, 1299025262068906347273438799331392] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B1678, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq1677 : B1677.tree = HexagonCover.NBand.M6667_6700.SplitData.node1677 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1678
  · rfl
  · rfl

theorem accepted1677 : B1677.accepted = true := by decide +kernel
theorem checked1677 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1677 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 1299025262068906347273438799331392]) := by
  rw [← treeEq1677]
  exact B1677.sound accepted1677
#print axioms checked1677

end HexagonCover.NBand.M6667_6700.SplitTree.Run0023
