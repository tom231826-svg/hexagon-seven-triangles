import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0019
import HexagonCover.NBand.M7500_7700.SplitTree.Run0020
import HexagonCover.NBand.M7500_7700.SplitTree.Run0021
import HexagonCover.NBand.M7500_7700.SplitTree.Run0022
import HexagonCover.NBand.M7500_7700.SplitTree.Run0024
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0025
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1756_1762 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1762 ![10384596192949733827821542456689025, 442865972957105096194, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0024.checked1762
def B1944 : Block := .branch 132 ![385, 1538, 6148, 24584, 5986493394212044715827068535409984783888156687695888, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 919).pointIds 919), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 999).pointIds 999)]
theorem treeEq1944 : B1944.tree = HexagonCover.NBand.M7500_7700.SplitData.node1944 := by
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

def B1943 : Block := .branch 157 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2865645758011185073687339798035314453518876704, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1944, (.leaf 5 (Common.fact 918).pointIds 918), (.leaf 0 [] 0)]
theorem treeEq1943 : B1943.tree = HexagonCover.NBand.M7500_7700.SplitData.node1943 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1944
  · rfl
  · rfl

def B1942 : Block := .branch 143 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 916).pointIds 916), B1943, (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq1942 : B1942.tree = HexagonCover.NBand.M7500_7700.SplitData.node1942 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1943
  · rfl

def B1941 : Block := .branch 125 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![B1942, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq1941 : B1941.tree = HexagonCover.NBand.M7500_7700.SplitData.node1941 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1942
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1940 : Block := .branch 151 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1941, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1940 : B1940.tree = HexagonCover.NBand.M7500_7700.SplitData.node1940 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1941
  · rfl

def B1939 : Block := .branch 170 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B1940, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1939 : B1939.tree = HexagonCover.NBand.M7500_7700.SplitData.node1939 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1940
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1938 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1939, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1938 : B1938.tree = HexagonCover.NBand.M7500_7700.SplitData.node1938 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1939
  · rfl

def B1937 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1938, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1937 : B1937.tree = HexagonCover.NBand.M7500_7700.SplitData.node1937 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1938
  · rfl
  · rfl

def B1761 : Block := .branch 68 ![10384596192949733827821542456689025, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 994).pointIds 994), Tip1756_1762, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B1937]
theorem treeEq1761 : B1761.tree = HexagonCover.NBand.M7500_7700.SplitData.node1761 := by
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
  · exact treeEq1937

def B1760 : Block := .branch 91 ![10384593717069655257060992658440577, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1761, (.leaf 1 (Common.fact 338).pointIds 338), (.leaf 2 (Common.fact 339).pointIds 339), (.leaf 3 (Common.fact 340).pointIds 340), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 993).pointIds 993)]
theorem treeEq1760 : B1760.tree = HexagonCover.NBand.M7500_7700.SplitData.node1760 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1761
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1759 : Block := .branch 113 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1760, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1759 : B1759.tree = HexagonCover.NBand.M7500_7700.SplitData.node1759 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1760
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1758 : Block := .branch 144 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1759, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq1758 : B1758.tree = HexagonCover.NBand.M7500_7700.SplitData.node1758 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1759
  · rfl

def B1757 : Block := .branch 149 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1758, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1757 : B1757.tree = HexagonCover.NBand.M7500_7700.SplitData.node1757 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1758
  · rfl
  · rfl

def B1756 : Block := .branch 161 ![385, 147718067777752270338, 18446884811197913092, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B1757]
theorem treeEq1756 : B1756.tree = HexagonCover.NBand.M7500_7700.SplitData.node1756 := by
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
  · exact treeEq1757

theorem accepted1756 : B1756.accepted = true := by decide +kernel
theorem checked1756 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1756 (maskNeeds ![385, 147718067777752270338, 18446884811197913092, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1756]
  exact B1756.sound accepted1756
#print axioms checked1756

def Tip1459_1464 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1464 ![385, 302231599018845369533954, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0019.checked1464
def Tip1459_1563 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1563 ![385, 147718067777752270338, 18446884811197913092, 79286209843071771272510726152, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0020.checked1563
def Tip1459_1598 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1598 ![385, 147718067777752270338, 18446884811197913092, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0021.checked1598
def Tip1459_1655 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1655 ![385, 147718067777752270338, 18446884811197913092, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0022.checked1655
def Tip1459_1756 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1756 ![385, 147718067777752270338, 18446884811197913092, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] checked1756
def B1562 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 992).pointIds 992), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 898).pointIds 898)]
theorem treeEq1562 : B1562.tree = HexagonCover.NBand.M7500_7700.SplitData.node1562 := by
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

def B1561 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778076675553987891277026333245081911360] ![(.leaf 0 (Common.fact 986).pointIds 986), (.leaf 1 (Common.fact 987).pointIds 987), (.leaf 2 (Common.fact 988).pointIds 988), (.leaf 3 (Common.fact 989).pointIds 989), B1562, (.leaf 5 (Common.fact 990).pointIds 990), (.leaf 6 (Common.fact 991).pointIds 991)]
theorem treeEq1561 : B1561.tree = HexagonCover.NBand.M7500_7700.SplitData.node1561 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1562
  · rfl
  · rfl

def B1560 : Block := .branch 112 ![1496577676626887123536438386009406733953603895034241, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B1561]
theorem treeEq1560 : B1560.tree = HexagonCover.NBand.M7500_7700.SplitData.node1560 := by
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
  · exact treeEq1561

def B1559 : Block := .branch 125 ![1496577676626844588240573268701473812127674924007809, 1538, 6148, 79228162514264337593543974920, 98320, 2854495385411919762116571938898990272765886496, 21778071483257129356449397802748752691264] ![B1560, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 984).pointIds 984)]
theorem treeEq1559 : B1559.tree = HexagonCover.NBand.M7500_7700.SplitData.node1559 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1560
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1558 : Block := .branch 151 ![1496577676626844588240573268701473812127674924007809, 1538, 6148, 79228162514264337593543974920, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1559, (.leaf 6 (Common.fact 983).pointIds 983)]
theorem treeEq1558 : B1558.tree = HexagonCover.NBand.M7500_7700.SplitData.node1558 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1559
  · rfl

def B1557 : Block := .branch 170 ![385, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 21778071483257129356449397802748752691264] ![B1558, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 895).pointIds 895)]
theorem treeEq1557 : B1557.tree = HexagonCover.NBand.M7500_7700.SplitData.node1557 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1558
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1556 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1557, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1556 : B1556.tree = HexagonCover.NBand.M7500_7700.SplitData.node1556 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1557
  · rfl

def B1555 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1556, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 894).pointIds 894)]
theorem treeEq1555 : B1555.tree = HexagonCover.NBand.M7500_7700.SplitData.node1555 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1556
  · rfl
  · rfl

def B1463 : Block := .branch 78 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), Tip1459_1464, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1555]
theorem treeEq1463 : B1463.tree = HexagonCover.NBand.M7500_7700.SplitData.node1463 := by
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
  · exact treeEq1555

def B1462 : Block := .branch 74 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), B1463, Tip1459_1563, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq1462 : B1462.tree = HexagonCover.NBand.M7500_7700.SplitData.node1462 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1463
  · rfl
  · rfl
  · rfl
  · rfl

def B1461 : Block := .branch 73 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), B1462, Tip1459_1598, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq1461 : B1461.tree = HexagonCover.NBand.M7500_7700.SplitData.node1461 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1462
  · rfl
  · rfl
  · rfl
  · rfl

def B1460 : Block := .branch 72 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), B1461, Tip1459_1655, (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1460 : B1460.tree = HexagonCover.NBand.M7500_7700.SplitData.node1460 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1461
  · rfl
  · rfl
  · rfl
  · rfl

def B1459 : Block := .branch 71 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 348).pointIds 348), (.leaf 1 (Common.fact 349).pointIds 349), B1460, Tip1459_1756, (.leaf 4 (Common.fact 350).pointIds 350), (.leaf 5 (Common.fact 351).pointIds 351), (.leaf 0 [] 0)]
theorem treeEq1459 : B1459.tree = HexagonCover.NBand.M7500_7700.SplitData.node1459 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1460
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1459 : B1459.accepted = true := by decide +kernel
theorem checked1459 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1459 (maskNeeds ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1459]
  exact B1459.sound accepted1459
#print axioms checked1459

def Tip1457_1459 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1459 ![385, 147718067777752270338, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] checked1459
def B1952 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5986310706518267388703763105636723235948516278894608, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 1003).pointIds 1003), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq1952 : B1952.tree = HexagonCover.NBand.M7500_7700.SplitData.node1952 := by
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

def B1951 : Block := .branch 133 ![385, 1538, 6148, 79247505327378171660339273736, 5986310706507378352962293074805895248510699696128016, 393248, 21778076675553987589193145382177464647744] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), B1952, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1002).pointIds 1002)]
theorem treeEq1951 : B1951.tree = HexagonCover.NBand.M7500_7700.SplitData.node1951 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1952
  · rfl
  · rfl

def B1950 : Block := .branch 112 ![1496577676626887123536438386009406733953603895034241, 1538, 6148, 79247505327378171660339273736, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B1951]
theorem treeEq1950 : B1950.tree = HexagonCover.NBand.M7500_7700.SplitData.node1950 := by
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
  · exact treeEq1951

def B1949 : Block := .branch 125 ![1496577676626844588240573268701473812127674924007809, 1538, 6148, 79247505327378171660339273736, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 21778071483257129054365516851681135427648] ![B1950, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 1001).pointIds 1001)]
theorem treeEq1949 : B1949.tree = HexagonCover.NBand.M7500_7700.SplitData.node1949 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1950
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1948 : Block := .branch 151 ![1496577676626844588240573268701473812127674924007809, 1538, 6148, 79247505327378171660339273736, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1949, (.leaf 6 (Common.fact 1000).pointIds 1000)]
theorem treeEq1948 : B1948.tree = HexagonCover.NBand.M7500_7700.SplitData.node1948 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1949
  · rfl

def B1947 : Block := .branch 170 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 21778071483257129054365516851681135427648] ![B1948, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 921).pointIds 921)]
theorem treeEq1947 : B1947.tree = HexagonCover.NBand.M7500_7700.SplitData.node1947 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1948
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1946 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1947, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1946 : B1946.tree = HexagonCover.NBand.M7500_7700.SplitData.node1946 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1947
  · rfl

def B1945 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1946, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq1945 : B1945.tree = HexagonCover.NBand.M7500_7700.SplitData.node1945 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1946
  · rfl
  · rfl

def B1458 : Block := .branch 67 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 233).pointIds 233), Tip1457_1459, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), B1945]
theorem treeEq1458 : B1458.tree = HexagonCover.NBand.M7500_7700.SplitData.node1458 := by
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
  · exact treeEq1945

def B1956 : Block := .branch 100 ![1496577676626844588240573268701473812127674924007809, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq1956 : B1956.tree = HexagonCover.NBand.M7500_7700.SplitData.node1956 := by
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
  · rfl

def B1955 : Block := .branch 170 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 21778071483256974311749925714704515727424] ![B1956, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 862).pointIds 862)]
theorem treeEq1955 : B1955.tree = HexagonCover.NBand.M7500_7700.SplitData.node1955 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1956
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1954 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1955, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1954 : B1954.tree = HexagonCover.NBand.M7500_7700.SplitData.node1954 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1955
  · rfl

def B1953 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1954, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq1953 : B1953.tree = HexagonCover.NBand.M7500_7700.SplitData.node1953 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1954
  · rfl
  · rfl

def B1457 : Block := .branch 65 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B1458, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B1953]
theorem treeEq1457 : B1457.tree = HexagonCover.NBand.M7500_7700.SplitData.node1457 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1458
  · rfl
  · rfl
  · rfl
  · exact treeEq1953

theorem accepted1457 : B1457.accepted = true := by decide +kernel
theorem checked1457 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1457 (maskNeeds ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1457]
  exact B1457.sound accepted1457
#print axioms checked1457

def B1444 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 588).pointIds 588), (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 213).pointIds 213)]
theorem treeEq1444 : B1444.tree = HexagonCover.NBand.M7500_7700.SplitData.node1444 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1443 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 1496577676626844609009760702840784326249660241281056, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), B1444, (.leaf 5 (Common.fact 730).pointIds 730), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1443 : B1443.tree = HexagonCover.NBand.M7500_7700.SplitData.node1443 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1444
  · rfl
  · rfl

def B1442 : Block := .branch 170 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), B1443, (.leaf 6 (Common.fact 725).pointIds 725)]
theorem treeEq1442 : B1442.tree = HexagonCover.NBand.M7500_7700.SplitData.node1442 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1443
  · rfl

def B1441 : Block := .branch 88 ![288230376151712129, 302231599018845369533954, 18446884811197913092, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1442]
theorem treeEq1441 : B1441.tree = HexagonCover.NBand.M7500_7700.SplitData.node1441 := by
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
  · exact treeEq1442

def B1440 : Block := .branch 78 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 142).pointIds 142), B1441, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 199).pointIds 199)]
theorem treeEq1440 : B1440.tree = HexagonCover.NBand.M7500_7700.SplitData.node1440 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1441
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1439 : Block := .branch 133 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1440]
theorem treeEq1439 : B1439.tree = HexagonCover.NBand.M7500_7700.SplitData.node1439 := by
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
  · exact treeEq1440

def B1438 : Block := .branch 157 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1439, (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 0 [] 0)]
theorem treeEq1438 : B1438.tree = HexagonCover.NBand.M7500_7700.SplitData.node1438 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1439
  · rfl
  · rfl

def B1437 : Block := .branch 114 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 184).pointIds 184), (.leaf 3 (Common.fact 185).pointIds 185), (.leaf 4 (Common.fact 186).pointIds 186), B1438, (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq1437 : B1437.tree = HexagonCover.NBand.M7500_7700.SplitData.node1437 := by
  change Tree.branch (114 : Fin 173) _ = Tree.branch (114 : Fin 173) _
  apply congrArg (Tree.branch (114 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1438
  · rfl

def B1436 : Block := .branch 65 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B1437, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq1436 : B1436.tree = HexagonCover.NBand.M7500_7700.SplitData.node1436 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1437
  · rfl
  · rfl
  · rfl
  · rfl

def B1435 : Block := .branch 67 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 233).pointIds 233), B1436, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq1435 : B1435.tree = HexagonCover.NBand.M7500_7700.SplitData.node1435 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1436
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1434 : Block := .branch 122 ![288230376151712129, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 111).pointIds 111), B1435]
theorem treeEq1434 : B1434.tree = HexagonCover.NBand.M7500_7700.SplitData.node1434 := by
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
  · exact treeEq1435

def B1433 : Block := .branch 138 ![288230376151712129, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B1434, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq1433 : B1433.tree = HexagonCover.NBand.M7500_7700.SplitData.node1433 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1434
  · rfl
  · rfl

def B1432 : Block := .branch 144 ![288230376151712129, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1433, (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1432 : B1432.tree = HexagonCover.NBand.M7500_7700.SplitData.node1432 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1433
  · rfl

def B1431 : Block := .branch 124 ![288230376151712129, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B1432]
theorem treeEq1431 : B1431.tree = HexagonCover.NBand.M7500_7700.SplitData.node1431 := by
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
  · exact treeEq1432

theorem accepted1431 : B1431.accepted = true := by decide +kernel
theorem checked1431 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1431 (maskNeeds ![288230376151712129, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1431]
  exact B1431.sound accepted1431
#print axioms checked1431

def Tip1430_1457 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1457 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] checked1457
def Tip1430_1431 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1431 ![288230376151712129, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] checked1431
def B1456 : Block := .branch 91 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 1496577676648627987020407254488838627316000162840640] ![(.leaf 0 (Common.fact 337).pointIds 337), (.leaf 1 (Common.fact 338).pointIds 338), (.leaf 2 (Common.fact 339).pointIds 339), (.leaf 3 (Common.fact 340).pointIds 340), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq1456 : B1456.tree = HexagonCover.NBand.M7500_7700.SplitData.node1456 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1455 : Block := .branch 170 ![576460752303423873, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 21783398779833985787364815188325238833216] ![(.leaf 0 (Common.fact 929).pointIds 929), (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), B1456]
theorem treeEq1455 : B1455.tree = HexagonCover.NBand.M7500_7700.SplitData.node1455 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1456

def B1454 : Block := .branch 171 ![576460752303423873, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706855827496689334061392390846520830344658960, 393248, 21783398779833985787364815188325238833216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 928).pointIds 928), B1455, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1454 : B1454.tree = HexagonCover.NBand.M7500_7700.SplitData.node1454 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1455
  · rfl

def B1453 : Block := .branch 172 ![576460752303423873, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21783398779833985787364815188325238833216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1454, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq1453 : B1453.tree = HexagonCover.NBand.M7500_7700.SplitData.node1453 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1454
  · rfl
  · rfl

def B1452 : Block := .branch 113 ![576460752303423873, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21783388395240268717709558127332580393024] ![(.leaf 0 (Common.fact 239).pointIds 239), (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), B1453]
theorem treeEq1452 : B1452.tree = HexagonCover.NBand.M7500_7700.SplitData.node1452 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1453

def B1451 : Block := .branch 65 ![576460752303423873, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B1452, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq1451 : B1451.tree = HexagonCover.NBand.M7500_7700.SplitData.node1451 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1452
  · rfl
  · rfl
  · rfl
  · rfl

def B1450 : Block := .branch 67 ![576460752303423873, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 233).pointIds 233), B1451, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq1450 : B1450.tree = HexagonCover.NBand.M7500_7700.SplitData.node1450 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1451
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1449 : Block := .branch 122 ![576460752303423873, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 111).pointIds 111), B1450]
theorem treeEq1449 : B1449.tree = HexagonCover.NBand.M7500_7700.SplitData.node1449 := by
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
  · exact treeEq1450

def B1448 : Block := .branch 138 ![576460752303423873, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B1449, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq1448 : B1448.tree = HexagonCover.NBand.M7500_7700.SplitData.node1448 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1449
  · rfl
  · rfl

def B1447 : Block := .branch 144 ![576460752303423873, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1448, (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1447 : B1447.tree = HexagonCover.NBand.M7500_7700.SplitData.node1447 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1448
  · rfl

def B1446 : Block := .branch 124 ![576460752303423873, 144115188075857410, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B1447]
theorem treeEq1446 : B1446.tree = HexagonCover.NBand.M7500_7700.SplitData.node1446 := by
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
  · exact treeEq1447

def B1445 : Block := .branch 59 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![B1446, Tip1430_1457, (.leaf 2 (Common.fact 227).pointIds 227), (.leaf 3 (Common.fact 228).pointIds 228), (.leaf 4 (Common.fact 229).pointIds 229), (.leaf 5 (Common.fact 230).pointIds 230), (.leaf 6 (Common.fact 231).pointIds 231)]
theorem treeEq1445 : B1445.tree = HexagonCover.NBand.M7500_7700.SplitData.node1445 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1446
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1430 : Block := .branch 58 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![Tip1430_1431, B1445, (.leaf 2 (Common.fact 167).pointIds 167), (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq1430 : B1430.tree = HexagonCover.NBand.M7500_7700.SplitData.node1430 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1445
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1430 : B1430.accepted = true := by decide +kernel
theorem checked1430 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1430 (maskNeeds ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1430]
  exact B1430.sound accepted1430
#print axioms checked1430

end HexagonCover.NBand.M7500_7700.SplitTree.Run0025
