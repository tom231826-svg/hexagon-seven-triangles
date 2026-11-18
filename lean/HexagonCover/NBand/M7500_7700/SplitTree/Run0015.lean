import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0014
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0015
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1205 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1205 : B1205.tree = HexagonCover.NBand.M7500_7700.SplitData.node1205 := by
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

def B1204 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1205]
theorem treeEq1204 : B1204.tree = HexagonCover.NBand.M7500_7700.SplitData.node1204 := by
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
  · exact treeEq1205

def B1203 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1204, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1203 : B1203.tree = HexagonCover.NBand.M7500_7700.SplitData.node1203 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1204
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1202 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1203, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1202 : B1202.tree = HexagonCover.NBand.M7500_7700.SplitData.node1202 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1203
  · rfl

def B1201 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1202, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1201 : B1201.tree = HexagonCover.NBand.M7500_7700.SplitData.node1201 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1202
  · rfl
  · rfl

def B1200 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1201]
theorem treeEq1200 : B1200.tree = HexagonCover.NBand.M7500_7700.SplitData.node1200 := by
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
  · exact treeEq1201

def B1211 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1211 : B1211.tree = HexagonCover.NBand.M7500_7700.SplitData.node1211 := by
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

def B1210 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1211, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1210 : B1210.tree = HexagonCover.NBand.M7500_7700.SplitData.node1210 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1211
  · rfl
  · rfl

def B1209 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1210]
theorem treeEq1209 : B1209.tree = HexagonCover.NBand.M7500_7700.SplitData.node1209 := by
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
  · exact treeEq1210

def B1208 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1209, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1208 : B1208.tree = HexagonCover.NBand.M7500_7700.SplitData.node1208 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1209
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1207 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1208, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1207 : B1207.tree = HexagonCover.NBand.M7500_7700.SplitData.node1207 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1208
  · rfl

def B1206 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1207, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1206 : B1206.tree = HexagonCover.NBand.M7500_7700.SplitData.node1206 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1207
  · rfl
  · rfl

def B1199 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1200, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1206]
theorem treeEq1199 : B1199.tree = HexagonCover.NBand.M7500_7700.SplitData.node1199 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1200
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1206

def B1216 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1216 : B1216.tree = HexagonCover.NBand.M7500_7700.SplitData.node1216 := by
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

def B1215 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1216]
theorem treeEq1215 : B1215.tree = HexagonCover.NBand.M7500_7700.SplitData.node1215 := by
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
  · exact treeEq1216

def B1214 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1215, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1214 : B1214.tree = HexagonCover.NBand.M7500_7700.SplitData.node1214 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1215
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1213 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1214, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1213 : B1213.tree = HexagonCover.NBand.M7500_7700.SplitData.node1213 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1214
  · rfl

def B1212 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1213, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1212 : B1212.tree = HexagonCover.NBand.M7500_7700.SplitData.node1212 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1213
  · rfl
  · rfl

def B1198 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1199, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1212]
theorem treeEq1198 : B1198.tree = HexagonCover.NBand.M7500_7700.SplitData.node1198 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1199
  · rfl
  · rfl
  · rfl
  · exact treeEq1212

theorem accepted1198 : B1198.accepted = true := by decide +kernel
theorem checked1198 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1198 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1198]
  exact B1198.sound accepted1198
#print axioms checked1198

def Tip1158_1159 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1159 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0014.checked1159
def B1185 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1185 : B1185.tree = HexagonCover.NBand.M7500_7700.SplitData.node1185 := by
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

def B1184 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1185]
theorem treeEq1184 : B1184.tree = HexagonCover.NBand.M7500_7700.SplitData.node1184 := by
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
  · exact treeEq1185

def B1183 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1184, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1183 : B1183.tree = HexagonCover.NBand.M7500_7700.SplitData.node1183 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1184
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1182 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1183, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1182 : B1182.tree = HexagonCover.NBand.M7500_7700.SplitData.node1182 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1183
  · rfl

def B1181 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1182, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1181 : B1181.tree = HexagonCover.NBand.M7500_7700.SplitData.node1181 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1182
  · rfl
  · rfl

def B1180 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1181]
theorem treeEq1180 : B1180.tree = HexagonCover.NBand.M7500_7700.SplitData.node1180 := by
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
  · exact treeEq1181

def B1191 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1191 : B1191.tree = HexagonCover.NBand.M7500_7700.SplitData.node1191 := by
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

def B1190 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1191, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1190 : B1190.tree = HexagonCover.NBand.M7500_7700.SplitData.node1190 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1191
  · rfl
  · rfl

def B1189 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1190]
theorem treeEq1189 : B1189.tree = HexagonCover.NBand.M7500_7700.SplitData.node1189 := by
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
  · exact treeEq1190

def B1188 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1189, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1188 : B1188.tree = HexagonCover.NBand.M7500_7700.SplitData.node1188 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1189
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1187 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1188, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1187 : B1187.tree = HexagonCover.NBand.M7500_7700.SplitData.node1187 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1188
  · rfl

def B1186 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1187, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1186 : B1186.tree = HexagonCover.NBand.M7500_7700.SplitData.node1186 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1187
  · rfl
  · rfl

def B1179 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1180, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1186]
theorem treeEq1179 : B1179.tree = HexagonCover.NBand.M7500_7700.SplitData.node1179 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1180
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1186

def B1196 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1196 : B1196.tree = HexagonCover.NBand.M7500_7700.SplitData.node1196 := by
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

def B1195 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1196]
theorem treeEq1195 : B1195.tree = HexagonCover.NBand.M7500_7700.SplitData.node1195 := by
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
  · exact treeEq1196

def B1194 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1195, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1194 : B1194.tree = HexagonCover.NBand.M7500_7700.SplitData.node1194 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1195
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1193 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1194, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1193 : B1193.tree = HexagonCover.NBand.M7500_7700.SplitData.node1193 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1194
  · rfl

def B1192 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1193, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1192 : B1192.tree = HexagonCover.NBand.M7500_7700.SplitData.node1192 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1193
  · rfl
  · rfl

def B1178 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1179, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1192]
theorem treeEq1178 : B1178.tree = HexagonCover.NBand.M7500_7700.SplitData.node1178 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1179
  · rfl
  · rfl
  · rfl
  · exact treeEq1192

def B1158 : Block := .branch 74 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip1158_1159, B1178, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq1158 : B1158.tree = HexagonCover.NBand.M7500_7700.SplitData.node1158 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1178
  · rfl
  · rfl
  · rfl

theorem accepted1158 : B1158.accepted = true := by decide +kernel
theorem checked1158 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1158 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1158]
  exact B1158.sound accepted1158
#print axioms checked1158

def Tip1197_1198 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1198 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1198
def B1224 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1224 : B1224.tree = HexagonCover.NBand.M7500_7700.SplitData.node1224 := by
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

def B1223 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1224]
theorem treeEq1223 : B1223.tree = HexagonCover.NBand.M7500_7700.SplitData.node1223 := by
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
  · exact treeEq1224

def B1222 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1223, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1222 : B1222.tree = HexagonCover.NBand.M7500_7700.SplitData.node1222 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1223
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1221 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1222, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1221 : B1221.tree = HexagonCover.NBand.M7500_7700.SplitData.node1221 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1222
  · rfl

def B1220 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1221, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1220 : B1220.tree = HexagonCover.NBand.M7500_7700.SplitData.node1220 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1221
  · rfl
  · rfl

def B1219 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1220]
theorem treeEq1219 : B1219.tree = HexagonCover.NBand.M7500_7700.SplitData.node1219 := by
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
  · exact treeEq1220

def B1230 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1230 : B1230.tree = HexagonCover.NBand.M7500_7700.SplitData.node1230 := by
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

def B1229 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1230, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1229 : B1229.tree = HexagonCover.NBand.M7500_7700.SplitData.node1229 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1230
  · rfl
  · rfl

def B1228 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1229]
theorem treeEq1228 : B1228.tree = HexagonCover.NBand.M7500_7700.SplitData.node1228 := by
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
  · exact treeEq1229

def B1227 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1228, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1227 : B1227.tree = HexagonCover.NBand.M7500_7700.SplitData.node1227 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1228
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1226 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1227, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1226 : B1226.tree = HexagonCover.NBand.M7500_7700.SplitData.node1226 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1227
  · rfl

def B1225 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1226, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1225 : B1225.tree = HexagonCover.NBand.M7500_7700.SplitData.node1225 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1226
  · rfl
  · rfl

def B1218 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1219, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1225]
theorem treeEq1218 : B1218.tree = HexagonCover.NBand.M7500_7700.SplitData.node1218 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1219
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1225

def B1235 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1235 : B1235.tree = HexagonCover.NBand.M7500_7700.SplitData.node1235 := by
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

def B1234 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1235]
theorem treeEq1234 : B1234.tree = HexagonCover.NBand.M7500_7700.SplitData.node1234 := by
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
  · exact treeEq1235

def B1233 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1234, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1233 : B1233.tree = HexagonCover.NBand.M7500_7700.SplitData.node1233 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1234
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1232 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1233, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1232 : B1232.tree = HexagonCover.NBand.M7500_7700.SplitData.node1232 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1233
  · rfl

def B1231 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1232, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1231 : B1231.tree = HexagonCover.NBand.M7500_7700.SplitData.node1231 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1232
  · rfl
  · rfl

def B1217 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1218, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1231]
theorem treeEq1217 : B1217.tree = HexagonCover.NBand.M7500_7700.SplitData.node1217 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1218
  · rfl
  · rfl
  · rfl
  · exact treeEq1231

def B1197 : Block := .branch 74 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip1197_1198, B1217, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq1197 : B1197.tree = HexagonCover.NBand.M7500_7700.SplitData.node1197 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1217
  · rfl
  · rfl
  · rfl

theorem accepted1197 : B1197.accepted = true := by decide +kernel
theorem checked1197 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1197 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1197]
  exact B1197.sound accepted1197
#print axioms checked1197

def Tip1037_1107 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1107 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0014.checked1107
def Tip1037_1038 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1038 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0014.checked1038
def B1151 : Block := .branch 108 ![385, 1538, 6148, 79247505327378171660339273736, 649037107316853453566312041250832, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 910).pointIds 910), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 911).pointIds 911)]
theorem treeEq1151 : B1151.tree = HexagonCover.NBand.M7500_7700.SplitData.node1151 := by
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

def B1150 : Block := .branch 109 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664344581903655978362901889088] ![(.leaf 0 (Common.fact 904).pointIds 904), (.leaf 1 (Common.fact 905).pointIds 905), (.leaf 2 (Common.fact 906).pointIds 906), (.leaf 3 (Common.fact 907).pointIds 907), B1151, (.leaf 5 (Common.fact 908).pointIds 908), (.leaf 6 (Common.fact 909).pointIds 909)]
theorem treeEq1150 : B1150.tree = HexagonCover.NBand.M7500_7700.SplitData.node1150 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1151
  · rfl
  · rfl

def B1149 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1150]
theorem treeEq1149 : B1149.tree = HexagonCover.NBand.M7500_7700.SplitData.node1149 := by
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
  · exact treeEq1150

def B1148 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B1149, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1148 : B1148.tree = HexagonCover.NBand.M7500_7700.SplitData.node1148 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1147 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1148, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1147 : B1147.tree = HexagonCover.NBand.M7500_7700.SplitData.node1147 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1148
  · rfl

def B1146 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1147, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1146 : B1146.tree = HexagonCover.NBand.M7500_7700.SplitData.node1146 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1147
  · rfl
  · rfl

def B1106 : Block := .branch 68 ![10384593717070245552871351364092289, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), Tip1037_1107, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B1146]
theorem treeEq1106 : B1106.tree = HexagonCover.NBand.M7500_7700.SplitData.node1106 := by
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
  · exact treeEq1146

def B1105 : Block := .branch 113 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1106, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1105 : B1105.tree = HexagonCover.NBand.M7500_7700.SplitData.node1105 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1106
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1104 : Block := .branch 144 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1105, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq1104 : B1104.tree = HexagonCover.NBand.M7500_7700.SplitData.node1104 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1105
  · rfl

def B1103 : Block := .branch 149 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1104, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1103 : B1103.tree = HexagonCover.NBand.M7500_7700.SplitData.node1103 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1104
  · rfl
  · rfl

def B1102 : Block := .branch 161 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B1103]
theorem treeEq1102 : B1102.tree = HexagonCover.NBand.M7500_7700.SplitData.node1102 := by
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
  · exact treeEq1103

def B1037 : Block := .branch 73 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip1037_1038, B1102, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq1037 : B1037.tree = HexagonCover.NBand.M7500_7700.SplitData.node1037 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1102
  · rfl
  · rfl
  · rfl

theorem accepted1037 : B1037.accepted = true := by decide +kernel
theorem checked1037 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1037 (maskNeeds ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1037]
  exact B1037.sound accepted1037
#print axioms checked1037

end HexagonCover.NBand.M7500_7700.SplitTree.Run0015
