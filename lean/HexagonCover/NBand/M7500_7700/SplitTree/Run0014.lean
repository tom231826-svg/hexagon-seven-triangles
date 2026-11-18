import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0013
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0014
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1115 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1115 : B1115.tree = HexagonCover.NBand.M7500_7700.SplitData.node1115 := by
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

def B1114 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1115]
theorem treeEq1114 : B1114.tree = HexagonCover.NBand.M7500_7700.SplitData.node1114 := by
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
  · exact treeEq1115

def B1113 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1114, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1113 : B1113.tree = HexagonCover.NBand.M7500_7700.SplitData.node1113 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1114
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1112 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1113, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1112 : B1112.tree = HexagonCover.NBand.M7500_7700.SplitData.node1112 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1113
  · rfl

def B1111 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1112, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1111 : B1111.tree = HexagonCover.NBand.M7500_7700.SplitData.node1111 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1112
  · rfl
  · rfl

def B1110 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1111]
theorem treeEq1110 : B1110.tree = HexagonCover.NBand.M7500_7700.SplitData.node1110 := by
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
  · exact treeEq1111

def B1121 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1121 : B1121.tree = HexagonCover.NBand.M7500_7700.SplitData.node1121 := by
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

def B1120 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1121, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1120 : B1120.tree = HexagonCover.NBand.M7500_7700.SplitData.node1120 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1121
  · rfl
  · rfl

def B1119 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1120]
theorem treeEq1119 : B1119.tree = HexagonCover.NBand.M7500_7700.SplitData.node1119 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1120

def B1118 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1119, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1118 : B1118.tree = HexagonCover.NBand.M7500_7700.SplitData.node1118 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1119
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1117 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1118, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1117 : B1117.tree = HexagonCover.NBand.M7500_7700.SplitData.node1117 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1118
  · rfl

def B1116 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1117, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1116 : B1116.tree = HexagonCover.NBand.M7500_7700.SplitData.node1116 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1117
  · rfl
  · rfl

def B1109 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1110, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1116]
theorem treeEq1109 : B1109.tree = HexagonCover.NBand.M7500_7700.SplitData.node1109 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1110
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1116

def B1126 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1126 : B1126.tree = HexagonCover.NBand.M7500_7700.SplitData.node1126 := by
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

def B1125 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1126]
theorem treeEq1125 : B1125.tree = HexagonCover.NBand.M7500_7700.SplitData.node1125 := by
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
  · exact treeEq1126

def B1124 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1125, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1124 : B1124.tree = HexagonCover.NBand.M7500_7700.SplitData.node1124 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1125
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1123 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1124, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1123 : B1123.tree = HexagonCover.NBand.M7500_7700.SplitData.node1123 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1124
  · rfl

def B1122 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1123, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1122 : B1122.tree = HexagonCover.NBand.M7500_7700.SplitData.node1122 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1123
  · rfl
  · rfl

def B1108 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1109, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1122]
theorem treeEq1108 : B1108.tree = HexagonCover.NBand.M7500_7700.SplitData.node1108 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1109
  · rfl
  · rfl
  · rfl
  · exact treeEq1122

theorem accepted1108 : B1108.accepted = true := by decide +kernel
theorem checked1108 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1108 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1108]
  exact B1108.sound accepted1108
#print axioms checked1108

def Tip1107_1108 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1108 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1108
def B1134 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1134 : B1134.tree = HexagonCover.NBand.M7500_7700.SplitData.node1134 := by
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

def B1133 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1134]
theorem treeEq1133 : B1133.tree = HexagonCover.NBand.M7500_7700.SplitData.node1133 := by
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
  · exact treeEq1134

def B1132 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1133, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1132 : B1132.tree = HexagonCover.NBand.M7500_7700.SplitData.node1132 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1133
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1131 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1132, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1131 : B1131.tree = HexagonCover.NBand.M7500_7700.SplitData.node1131 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1132
  · rfl

def B1130 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1131, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1130 : B1130.tree = HexagonCover.NBand.M7500_7700.SplitData.node1130 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1131
  · rfl
  · rfl

def B1129 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1130]
theorem treeEq1129 : B1129.tree = HexagonCover.NBand.M7500_7700.SplitData.node1129 := by
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
  · exact treeEq1130

def B1140 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1140 : B1140.tree = HexagonCover.NBand.M7500_7700.SplitData.node1140 := by
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

def B1139 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1140, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1139 : B1139.tree = HexagonCover.NBand.M7500_7700.SplitData.node1139 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1140
  · rfl
  · rfl

def B1138 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1139]
theorem treeEq1138 : B1138.tree = HexagonCover.NBand.M7500_7700.SplitData.node1138 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1139

def B1137 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1138, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1137 : B1137.tree = HexagonCover.NBand.M7500_7700.SplitData.node1137 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1138
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1136 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1137, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1136 : B1136.tree = HexagonCover.NBand.M7500_7700.SplitData.node1136 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1137
  · rfl

def B1135 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1136, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1135 : B1135.tree = HexagonCover.NBand.M7500_7700.SplitData.node1135 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1136
  · rfl
  · rfl

def B1128 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1129, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1135]
theorem treeEq1128 : B1128.tree = HexagonCover.NBand.M7500_7700.SplitData.node1128 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1129
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1135

def B1145 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1145 : B1145.tree = HexagonCover.NBand.M7500_7700.SplitData.node1145 := by
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

def B1144 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1145]
theorem treeEq1144 : B1144.tree = HexagonCover.NBand.M7500_7700.SplitData.node1144 := by
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
  · exact treeEq1145

def B1143 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1144, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1143 : B1143.tree = HexagonCover.NBand.M7500_7700.SplitData.node1143 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1144
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1142 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1143, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1142 : B1142.tree = HexagonCover.NBand.M7500_7700.SplitData.node1142 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1143
  · rfl

def B1141 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1142, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1141 : B1141.tree = HexagonCover.NBand.M7500_7700.SplitData.node1141 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1142
  · rfl
  · rfl

def B1127 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1128, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1141]
theorem treeEq1127 : B1127.tree = HexagonCover.NBand.M7500_7700.SplitData.node1127 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1128
  · rfl
  · rfl
  · rfl
  · exact treeEq1141

def B1107 : Block := .branch 74 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip1107_1108, B1127, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq1107 : B1107.tree = HexagonCover.NBand.M7500_7700.SplitData.node1107 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1127
  · rfl
  · rfl
  · rfl

theorem accepted1107 : B1107.accepted = true := by decide +kernel
theorem checked1107 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1107 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1107]
  exact B1107.sound accepted1107
#print axioms checked1107

def Tip1038_1077 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1077 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0013.checked1077
def Tip1038_1039 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1039 ![590295810358705652097, 216172782113785346, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0013.checked1039
def B1101 : Block := .branch 108 ![385, 1538, 6148, 79247505327378171660339273736, 649037107316853453566312041250832, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 910).pointIds 910), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 911).pointIds 911)]
theorem treeEq1101 : B1101.tree = HexagonCover.NBand.M7500_7700.SplitData.node1101 := by
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

def B1100 : Block := .branch 109 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664344581903655978362901889088] ![(.leaf 0 (Common.fact 904).pointIds 904), (.leaf 1 (Common.fact 905).pointIds 905), (.leaf 2 (Common.fact 906).pointIds 906), (.leaf 3 (Common.fact 907).pointIds 907), B1101, (.leaf 5 (Common.fact 908).pointIds 908), (.leaf 6 (Common.fact 909).pointIds 909)]
theorem treeEq1100 : B1100.tree = HexagonCover.NBand.M7500_7700.SplitData.node1100 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1101
  · rfl
  · rfl

def B1099 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1100]
theorem treeEq1099 : B1099.tree = HexagonCover.NBand.M7500_7700.SplitData.node1099 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1100

def B1098 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B1099, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1098 : B1098.tree = HexagonCover.NBand.M7500_7700.SplitData.node1098 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1099
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1097 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1098, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1097 : B1097.tree = HexagonCover.NBand.M7500_7700.SplitData.node1097 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1098
  · rfl

def B1096 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1097, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1096 : B1096.tree = HexagonCover.NBand.M7500_7700.SplitData.node1096 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1097
  · rfl
  · rfl

def B1076 : Block := .branch 68 ![10384593717070245552871351364092289, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), Tip1038_1077, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B1096]
theorem treeEq1076 : B1076.tree = HexagonCover.NBand.M7500_7700.SplitData.node1076 := by
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
  · exact treeEq1096

def B1075 : Block := .branch 113 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1076, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1075 : B1075.tree = HexagonCover.NBand.M7500_7700.SplitData.node1075 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1076
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1074 : Block := .branch 144 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1075, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq1074 : B1074.tree = HexagonCover.NBand.M7500_7700.SplitData.node1074 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1075
  · rfl

def B1073 : Block := .branch 149 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1074, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1073 : B1073.tree = HexagonCover.NBand.M7500_7700.SplitData.node1073 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1074
  · rfl
  · rfl

def B1072 : Block := .branch 161 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286209843071771272510726152, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B1073]
theorem treeEq1072 : B1072.tree = HexagonCover.NBand.M7500_7700.SplitData.node1072 := by
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
  · exact treeEq1073

def B1038 : Block := .branch 74 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip1038_1039, B1072, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq1038 : B1038.tree = HexagonCover.NBand.M7500_7700.SplitData.node1038 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1072
  · rfl
  · rfl
  · rfl

theorem accepted1038 : B1038.accepted = true := by decide +kernel
theorem checked1038 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1038 (maskNeeds ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1038]
  exact B1038.sound accepted1038
#print axioms checked1038

def B1166 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1166 : B1166.tree = HexagonCover.NBand.M7500_7700.SplitData.node1166 := by
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

def B1165 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1166]
theorem treeEq1165 : B1165.tree = HexagonCover.NBand.M7500_7700.SplitData.node1165 := by
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
  · exact treeEq1166

def B1164 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1165, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1164 : B1164.tree = HexagonCover.NBand.M7500_7700.SplitData.node1164 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1165
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1163 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1164, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1163 : B1163.tree = HexagonCover.NBand.M7500_7700.SplitData.node1163 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1164
  · rfl

def B1162 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1163, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1162 : B1162.tree = HexagonCover.NBand.M7500_7700.SplitData.node1162 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1163
  · rfl
  · rfl

def B1161 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1162]
theorem treeEq1161 : B1161.tree = HexagonCover.NBand.M7500_7700.SplitData.node1161 := by
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
  · exact treeEq1162

def B1172 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1172 : B1172.tree = HexagonCover.NBand.M7500_7700.SplitData.node1172 := by
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

def B1171 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1172, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1171 : B1171.tree = HexagonCover.NBand.M7500_7700.SplitData.node1171 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1172
  · rfl
  · rfl

def B1170 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1171]
theorem treeEq1170 : B1170.tree = HexagonCover.NBand.M7500_7700.SplitData.node1170 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1171

def B1169 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1170, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1169 : B1169.tree = HexagonCover.NBand.M7500_7700.SplitData.node1169 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1170
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1168 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1169, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1168 : B1168.tree = HexagonCover.NBand.M7500_7700.SplitData.node1168 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1169
  · rfl

def B1167 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1168, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1167 : B1167.tree = HexagonCover.NBand.M7500_7700.SplitData.node1167 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1168
  · rfl
  · rfl

def B1160 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1161, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1167]
theorem treeEq1160 : B1160.tree = HexagonCover.NBand.M7500_7700.SplitData.node1160 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1161
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1167

def B1177 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1177 : B1177.tree = HexagonCover.NBand.M7500_7700.SplitData.node1177 := by
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

def B1176 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1177]
theorem treeEq1176 : B1176.tree = HexagonCover.NBand.M7500_7700.SplitData.node1176 := by
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
  · exact treeEq1177

def B1175 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1176, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1175 : B1175.tree = HexagonCover.NBand.M7500_7700.SplitData.node1175 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1176
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1174 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1175, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1174 : B1174.tree = HexagonCover.NBand.M7500_7700.SplitData.node1174 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1175
  · rfl

def B1173 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1174, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1173 : B1173.tree = HexagonCover.NBand.M7500_7700.SplitData.node1173 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1174
  · rfl
  · rfl

def B1159 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1160, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1173]
theorem treeEq1159 : B1159.tree = HexagonCover.NBand.M7500_7700.SplitData.node1159 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1160
  · rfl
  · rfl
  · rfl
  · exact treeEq1173

theorem accepted1159 : B1159.accepted = true := by decide +kernel
theorem checked1159 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1159 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1159]
  exact B1159.sound accepted1159
#print axioms checked1159

end HexagonCover.NBand.M7500_7700.SplitTree.Run0014
