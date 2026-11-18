import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0020
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0021
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1598_1604 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1604 ![10384596192949733827821542456689025, 442865972957105096194, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0020.checked1604
def B1654 : Block := .branch 132 ![385, 1538, 6148, 24584, 5986493394212044715827068535409984783888156687695888, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 919).pointIds 919), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 999).pointIds 999)]
theorem treeEq1654 : B1654.tree = HexagonCover.NBand.M7500_7700.SplitData.node1654 := by
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

def B1653 : Block := .branch 157 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2865645758011185073687339798035314453518876704, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1654, (.leaf 5 (Common.fact 918).pointIds 918), (.leaf 0 [] 0)]
theorem treeEq1653 : B1653.tree = HexagonCover.NBand.M7500_7700.SplitData.node1653 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1654
  · rfl
  · rfl

def B1652 : Block := .branch 143 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 916).pointIds 916), B1653, (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq1652 : B1652.tree = HexagonCover.NBand.M7500_7700.SplitData.node1652 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1653
  · rfl

def B1651 : Block := .branch 125 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![B1652, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq1651 : B1651.tree = HexagonCover.NBand.M7500_7700.SplitData.node1651 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1652
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1650 : Block := .branch 151 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1651, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1650 : B1650.tree = HexagonCover.NBand.M7500_7700.SplitData.node1650 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1651
  · rfl

def B1649 : Block := .branch 170 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B1650, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1649 : B1649.tree = HexagonCover.NBand.M7500_7700.SplitData.node1649 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1650
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1648 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1649, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1648 : B1648.tree = HexagonCover.NBand.M7500_7700.SplitData.node1648 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1649
  · rfl

def B1647 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1648, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1647 : B1647.tree = HexagonCover.NBand.M7500_7700.SplitData.node1647 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1648
  · rfl
  · rfl

def B1603 : Block := .branch 68 ![10384596192949733827821542456689025, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 994).pointIds 994), Tip1598_1604, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B1647]
theorem treeEq1603 : B1603.tree = HexagonCover.NBand.M7500_7700.SplitData.node1603 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1647

def B1602 : Block := .branch 91 ![10384593717069655257060992658440577, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1603, (.leaf 1 (Common.fact 338).pointIds 338), (.leaf 2 (Common.fact 339).pointIds 339), (.leaf 3 (Common.fact 340).pointIds 340), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 993).pointIds 993)]
theorem treeEq1602 : B1602.tree = HexagonCover.NBand.M7500_7700.SplitData.node1602 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1603
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1601 : Block := .branch 113 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1602, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1601 : B1601.tree = HexagonCover.NBand.M7500_7700.SplitData.node1601 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1602
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1600 : Block := .branch 144 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1601, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq1600 : B1600.tree = HexagonCover.NBand.M7500_7700.SplitData.node1600 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1601
  · rfl

def B1599 : Block := .branch 149 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1600, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1599 : B1599.tree = HexagonCover.NBand.M7500_7700.SplitData.node1599 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1600
  · rfl
  · rfl

def B1598 : Block := .branch 161 ![385, 147718067777752270338, 18446884811197913092, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B1599]
theorem treeEq1598 : B1598.tree = HexagonCover.NBand.M7500_7700.SplitData.node1598 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1599

theorem accepted1598 : B1598.accepted = true := by decide +kernel
theorem checked1598 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1598 (maskNeeds ![385, 147718067777752270338, 18446884811197913092, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1598]
  exact B1598.sound accepted1598
#print axioms checked1598

def B1670 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1670 : B1670.tree = HexagonCover.NBand.M7500_7700.SplitData.node1670 := by
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

def B1669 : Block := .branch 100 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1670]
theorem treeEq1669 : B1669.tree = HexagonCover.NBand.M7500_7700.SplitData.node1669 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1670

def B1668 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1669, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1668 : B1668.tree = HexagonCover.NBand.M7500_7700.SplitData.node1668 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1669
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1667 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1668, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1667 : B1667.tree = HexagonCover.NBand.M7500_7700.SplitData.node1667 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1668
  · rfl

def B1666 : Block := .branch 142 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1667, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1666 : B1666.tree = HexagonCover.NBand.M7500_7700.SplitData.node1666 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1667
  · rfl
  · rfl

def B1665 : Block := .branch 88 ![10384596192949733827821542456689025, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1666]
theorem treeEq1665 : B1665.tree = HexagonCover.NBand.M7500_7700.SplitData.node1665 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1666

def B1678 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1678 : B1678.tree = HexagonCover.NBand.M7500_7700.SplitData.node1678 := by
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

def B1677 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439882511961202814204681700022584606784] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1678, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 997).pointIds 997)]
theorem treeEq1677 : B1677.tree = HexagonCover.NBand.M7500_7700.SplitData.node1677 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1678
  · rfl
  · rfl

def B1676 : Block := .branch 112 ![1496577676626887133921034578959140561775146351722881, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 996).pointIds 996), (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B1677]
theorem treeEq1676 : B1676.tree = HexagonCover.NBand.M7500_7700.SplitData.node1676 := by
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
  · exact treeEq1677

def B1675 : Block := .branch 125 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![B1676, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1675 : B1675.tree = HexagonCover.NBand.M7500_7700.SplitData.node1675 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1676
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1674 : Block := .branch 151 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1675, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1674 : B1674.tree = HexagonCover.NBand.M7500_7700.SplitData.node1674 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1675
  · rfl

def B1673 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1674, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1673 : B1673.tree = HexagonCover.NBand.M7500_7700.SplitData.node1673 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1674
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1672 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1673, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1672 : B1672.tree = HexagonCover.NBand.M7500_7700.SplitData.node1672 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1673
  · rfl

def B1671 : Block := .branch 172 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1672, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1671 : B1671.tree = HexagonCover.NBand.M7500_7700.SplitData.node1671 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1672
  · rfl
  · rfl

def B1664 : Block := .branch 78 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1665, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1671]
theorem treeEq1664 : B1664.tree = HexagonCover.NBand.M7500_7700.SplitData.node1664 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1665
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1671

theorem accepted1664 : B1664.accepted = true := by decide +kernel
theorem checked1664 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1664 (maskNeeds ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1664]
  exact B1664.sound accepted1664
#print axioms checked1664

def B1691 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1691 : B1691.tree = HexagonCover.NBand.M7500_7700.SplitData.node1691 := by
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

def B1690 : Block := .branch 100 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1691]
theorem treeEq1690 : B1690.tree = HexagonCover.NBand.M7500_7700.SplitData.node1690 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1691

def B1689 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1690, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1689 : B1689.tree = HexagonCover.NBand.M7500_7700.SplitData.node1689 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1690
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1688 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1689, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1688 : B1688.tree = HexagonCover.NBand.M7500_7700.SplitData.node1688 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1689
  · rfl

def B1687 : Block := .branch 142 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1688, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1687 : B1687.tree = HexagonCover.NBand.M7500_7700.SplitData.node1687 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1688
  · rfl
  · rfl

def B1686 : Block := .branch 88 ![10384596192949733827821542456689025, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1687]
theorem treeEq1686 : B1686.tree = HexagonCover.NBand.M7500_7700.SplitData.node1686 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1687

def B1699 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1699 : B1699.tree = HexagonCover.NBand.M7500_7700.SplitData.node1699 := by
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

def B1698 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439882511961202814204681700022584606784] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1699, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 997).pointIds 997)]
theorem treeEq1698 : B1698.tree = HexagonCover.NBand.M7500_7700.SplitData.node1698 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1699
  · rfl
  · rfl

def B1697 : Block := .branch 112 ![1496577676626887133921034578959140561775146351722881, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 996).pointIds 996), (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B1698]
theorem treeEq1697 : B1697.tree = HexagonCover.NBand.M7500_7700.SplitData.node1697 := by
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
  · exact treeEq1698

def B1696 : Block := .branch 125 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![B1697, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1696 : B1696.tree = HexagonCover.NBand.M7500_7700.SplitData.node1696 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1697
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1695 : Block := .branch 151 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1696, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1695 : B1695.tree = HexagonCover.NBand.M7500_7700.SplitData.node1695 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1696
  · rfl

def B1694 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1695, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1694 : B1694.tree = HexagonCover.NBand.M7500_7700.SplitData.node1694 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1695
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1693 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1694, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1693 : B1693.tree = HexagonCover.NBand.M7500_7700.SplitData.node1693 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1694
  · rfl

def B1692 : Block := .branch 172 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1693, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1692 : B1692.tree = HexagonCover.NBand.M7500_7700.SplitData.node1692 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1693
  · rfl
  · rfl

def B1685 : Block := .branch 78 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1686, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1692]
theorem treeEq1685 : B1685.tree = HexagonCover.NBand.M7500_7700.SplitData.node1685 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1686
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1692

theorem accepted1685 : B1685.accepted = true := by decide +kernel
theorem checked1685 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1685 (maskNeeds ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1685]
  exact B1685.sound accepted1685
#print axioms checked1685

def B1713 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1713 : B1713.tree = HexagonCover.NBand.M7500_7700.SplitData.node1713 := by
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

def B1712 : Block := .branch 100 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1713]
theorem treeEq1712 : B1712.tree = HexagonCover.NBand.M7500_7700.SplitData.node1712 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1713

def B1711 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1712, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1711 : B1711.tree = HexagonCover.NBand.M7500_7700.SplitData.node1711 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1712
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1710 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1711, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1710 : B1710.tree = HexagonCover.NBand.M7500_7700.SplitData.node1710 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1711
  · rfl

def B1709 : Block := .branch 142 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1710, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1709 : B1709.tree = HexagonCover.NBand.M7500_7700.SplitData.node1709 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1710
  · rfl
  · rfl

def B1708 : Block := .branch 88 ![10384596192949733827821542456689025, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1709]
theorem treeEq1708 : B1708.tree = HexagonCover.NBand.M7500_7700.SplitData.node1708 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1709

def B1721 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1721 : B1721.tree = HexagonCover.NBand.M7500_7700.SplitData.node1721 := by
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

def B1720 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439882511961202814204681700022584606784] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1721, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 997).pointIds 997)]
theorem treeEq1720 : B1720.tree = HexagonCover.NBand.M7500_7700.SplitData.node1720 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1721
  · rfl
  · rfl

def B1719 : Block := .branch 112 ![1496577676626887133921034578959140561775146351722881, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 996).pointIds 996), (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B1720]
theorem treeEq1719 : B1719.tree = HexagonCover.NBand.M7500_7700.SplitData.node1719 := by
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
  · exact treeEq1720

def B1718 : Block := .branch 125 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![B1719, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1718 : B1718.tree = HexagonCover.NBand.M7500_7700.SplitData.node1718 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1719
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1717 : Block := .branch 151 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1718, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1717 : B1717.tree = HexagonCover.NBand.M7500_7700.SplitData.node1717 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1718
  · rfl

def B1716 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1717, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1716 : B1716.tree = HexagonCover.NBand.M7500_7700.SplitData.node1716 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1717
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1715 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1716, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1715 : B1715.tree = HexagonCover.NBand.M7500_7700.SplitData.node1715 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1716
  · rfl

def B1714 : Block := .branch 172 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1715, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1714 : B1714.tree = HexagonCover.NBand.M7500_7700.SplitData.node1714 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1715
  · rfl
  · rfl

def B1707 : Block := .branch 78 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1708, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1714]
theorem treeEq1707 : B1707.tree = HexagonCover.NBand.M7500_7700.SplitData.node1707 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1708
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1714

theorem accepted1707 : B1707.accepted = true := by decide +kernel
theorem checked1707 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1707 (maskNeeds ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1707]
  exact B1707.sound accepted1707
#print axioms checked1707

def B1734 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1734 : B1734.tree = HexagonCover.NBand.M7500_7700.SplitData.node1734 := by
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

def B1733 : Block := .branch 100 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 979).pointIds 979), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1734]
theorem treeEq1733 : B1733.tree = HexagonCover.NBand.M7500_7700.SplitData.node1733 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1734

def B1732 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1733, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1732 : B1732.tree = HexagonCover.NBand.M7500_7700.SplitData.node1732 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1733
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1731 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1732, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1731 : B1731.tree = HexagonCover.NBand.M7500_7700.SplitData.node1731 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1732
  · rfl

def B1730 : Block := .branch 142 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1731, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1730 : B1730.tree = HexagonCover.NBand.M7500_7700.SplitData.node1730 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1731
  · rfl
  · rfl

def B1729 : Block := .branch 88 ![10384596192949733827821542456689025, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1730]
theorem treeEq1729 : B1729.tree = HexagonCover.NBand.M7500_7700.SplitData.node1729 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1730

def B1742 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1742 : B1742.tree = HexagonCover.NBand.M7500_7700.SplitData.node1742 := by
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

def B1741 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439882511961202814204681700022584606784] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1742, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 997).pointIds 997)]
theorem treeEq1741 : B1741.tree = HexagonCover.NBand.M7500_7700.SplitData.node1741 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1742
  · rfl
  · rfl

def B1740 : Block := .branch 112 ![1496577676626887133921034578959140561775146351722881, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 996).pointIds 996), (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B1741]
theorem treeEq1740 : B1740.tree = HexagonCover.NBand.M7500_7700.SplitData.node1740 := by
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
  · exact treeEq1741

def B1739 : Block := .branch 125 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![B1740, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1739 : B1739.tree = HexagonCover.NBand.M7500_7700.SplitData.node1739 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1740
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1738 : Block := .branch 151 ![1496577676626844598625169461651207639949217380696449, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1739, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1738 : B1738.tree = HexagonCover.NBand.M7500_7700.SplitData.node1738 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1739
  · rfl

def B1737 : Block := .branch 170 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1738, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1737 : B1737.tree = HexagonCover.NBand.M7500_7700.SplitData.node1737 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1738
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1736 : Block := .branch 171 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1737, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1736 : B1736.tree = HexagonCover.NBand.M7500_7700.SplitData.node1736 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1737
  · rfl

def B1735 : Block := .branch 172 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1736, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1735 : B1735.tree = HexagonCover.NBand.M7500_7700.SplitData.node1735 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1736
  · rfl
  · rfl

def B1728 : Block := .branch 78 ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1729, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1735]
theorem treeEq1728 : B1728.tree = HexagonCover.NBand.M7500_7700.SplitData.node1728 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1729
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1735

theorem accepted1728 : B1728.accepted = true := by decide +kernel
theorem checked1728 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1728 (maskNeeds ![10384596192949733827821542456689025, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1728]
  exact B1728.sound accepted1728
#print axioms checked1728

end HexagonCover.NBand.M7500_7700.SplitTree.Run0021
