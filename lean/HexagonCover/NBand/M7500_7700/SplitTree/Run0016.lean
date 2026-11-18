import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0016
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1257 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1257 : B1257.tree = HexagonCover.NBand.M7500_7700.SplitData.node1257 := by
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

def B1256 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1257]
theorem treeEq1256 : B1256.tree = HexagonCover.NBand.M7500_7700.SplitData.node1256 := by
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
  · exact treeEq1257

def B1255 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1256, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1255 : B1255.tree = HexagonCover.NBand.M7500_7700.SplitData.node1255 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1256
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1254 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1255, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1254 : B1254.tree = HexagonCover.NBand.M7500_7700.SplitData.node1254 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1255
  · rfl

def B1253 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1254, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1253 : B1253.tree = HexagonCover.NBand.M7500_7700.SplitData.node1253 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1254
  · rfl
  · rfl

def B1252 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1253]
theorem treeEq1252 : B1252.tree = HexagonCover.NBand.M7500_7700.SplitData.node1252 := by
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
  · exact treeEq1253

def B1263 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1263 : B1263.tree = HexagonCover.NBand.M7500_7700.SplitData.node1263 := by
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

def B1262 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1263, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1262 : B1262.tree = HexagonCover.NBand.M7500_7700.SplitData.node1262 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1263
  · rfl
  · rfl

def B1261 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1262]
theorem treeEq1261 : B1261.tree = HexagonCover.NBand.M7500_7700.SplitData.node1261 := by
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
  · exact treeEq1262

def B1260 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1261, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1260 : B1260.tree = HexagonCover.NBand.M7500_7700.SplitData.node1260 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1261
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1259 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1260, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1259 : B1259.tree = HexagonCover.NBand.M7500_7700.SplitData.node1259 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1260
  · rfl

def B1258 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1259, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1258 : B1258.tree = HexagonCover.NBand.M7500_7700.SplitData.node1258 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1259
  · rfl
  · rfl

def B1251 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1252, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1258]
theorem treeEq1251 : B1251.tree = HexagonCover.NBand.M7500_7700.SplitData.node1251 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1252
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1258

def B1268 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1268 : B1268.tree = HexagonCover.NBand.M7500_7700.SplitData.node1268 := by
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

def B1267 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1268]
theorem treeEq1267 : B1267.tree = HexagonCover.NBand.M7500_7700.SplitData.node1267 := by
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
  · exact treeEq1268

def B1266 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1267, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1266 : B1266.tree = HexagonCover.NBand.M7500_7700.SplitData.node1266 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1267
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1265 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1266, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1265 : B1265.tree = HexagonCover.NBand.M7500_7700.SplitData.node1265 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1266
  · rfl

def B1264 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1265, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1264 : B1264.tree = HexagonCover.NBand.M7500_7700.SplitData.node1264 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1265
  · rfl
  · rfl

def B1250 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1251, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1264]
theorem treeEq1250 : B1250.tree = HexagonCover.NBand.M7500_7700.SplitData.node1250 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1251
  · rfl
  · rfl
  · rfl
  · exact treeEq1264

theorem accepted1250 : B1250.accepted = true := by decide +kernel
theorem checked1250 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1250 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1250]
  exact B1250.sound accepted1250
#print axioms checked1250

def B1296 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1296 : B1296.tree = HexagonCover.NBand.M7500_7700.SplitData.node1296 := by
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

def B1295 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1296]
theorem treeEq1295 : B1295.tree = HexagonCover.NBand.M7500_7700.SplitData.node1295 := by
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
  · exact treeEq1296

def B1294 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1295, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1294 : B1294.tree = HexagonCover.NBand.M7500_7700.SplitData.node1294 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1295
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1293 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1294, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1293 : B1293.tree = HexagonCover.NBand.M7500_7700.SplitData.node1293 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1294
  · rfl

def B1292 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1293, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1292 : B1292.tree = HexagonCover.NBand.M7500_7700.SplitData.node1292 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1293
  · rfl
  · rfl

def B1291 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1292]
theorem treeEq1291 : B1291.tree = HexagonCover.NBand.M7500_7700.SplitData.node1291 := by
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
  · exact treeEq1292

def B1302 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1302 : B1302.tree = HexagonCover.NBand.M7500_7700.SplitData.node1302 := by
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

def B1301 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1302, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1301 : B1301.tree = HexagonCover.NBand.M7500_7700.SplitData.node1301 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1302
  · rfl
  · rfl

def B1300 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1301]
theorem treeEq1300 : B1300.tree = HexagonCover.NBand.M7500_7700.SplitData.node1300 := by
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
  · exact treeEq1301

def B1299 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1300, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1299 : B1299.tree = HexagonCover.NBand.M7500_7700.SplitData.node1299 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1300
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1298 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1299, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1298 : B1298.tree = HexagonCover.NBand.M7500_7700.SplitData.node1298 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1299
  · rfl

def B1297 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1298, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1297 : B1297.tree = HexagonCover.NBand.M7500_7700.SplitData.node1297 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1298
  · rfl
  · rfl

def B1290 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1291, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1297]
theorem treeEq1290 : B1290.tree = HexagonCover.NBand.M7500_7700.SplitData.node1290 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1291
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1297

def B1307 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1307 : B1307.tree = HexagonCover.NBand.M7500_7700.SplitData.node1307 := by
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

def B1306 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1307]
theorem treeEq1306 : B1306.tree = HexagonCover.NBand.M7500_7700.SplitData.node1306 := by
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
  · exact treeEq1307

def B1305 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1306, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1305 : B1305.tree = HexagonCover.NBand.M7500_7700.SplitData.node1305 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1306
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1304 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1305, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1304 : B1304.tree = HexagonCover.NBand.M7500_7700.SplitData.node1304 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1305
  · rfl

def B1303 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1304, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1303 : B1303.tree = HexagonCover.NBand.M7500_7700.SplitData.node1303 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1304
  · rfl
  · rfl

def B1289 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1290, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1303]
theorem treeEq1289 : B1289.tree = HexagonCover.NBand.M7500_7700.SplitData.node1289 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1290
  · rfl
  · rfl
  · rfl
  · exact treeEq1303

theorem accepted1289 : B1289.accepted = true := by decide +kernel
theorem checked1289 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1289 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1289]
  exact B1289.sound accepted1289
#print axioms checked1289

def Tip1249_1250 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1250 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1250
def B1276 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1276 : B1276.tree = HexagonCover.NBand.M7500_7700.SplitData.node1276 := by
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

def B1275 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1276]
theorem treeEq1275 : B1275.tree = HexagonCover.NBand.M7500_7700.SplitData.node1275 := by
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
  · exact treeEq1276

def B1274 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1275, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1274 : B1274.tree = HexagonCover.NBand.M7500_7700.SplitData.node1274 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1275
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1273 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1274, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1273 : B1273.tree = HexagonCover.NBand.M7500_7700.SplitData.node1273 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1274
  · rfl

def B1272 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1273, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1272 : B1272.tree = HexagonCover.NBand.M7500_7700.SplitData.node1272 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1273
  · rfl
  · rfl

def B1271 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1272]
theorem treeEq1271 : B1271.tree = HexagonCover.NBand.M7500_7700.SplitData.node1271 := by
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
  · exact treeEq1272

def B1282 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1282 : B1282.tree = HexagonCover.NBand.M7500_7700.SplitData.node1282 := by
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

def B1281 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1282, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1281 : B1281.tree = HexagonCover.NBand.M7500_7700.SplitData.node1281 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1282
  · rfl
  · rfl

def B1280 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1281]
theorem treeEq1280 : B1280.tree = HexagonCover.NBand.M7500_7700.SplitData.node1280 := by
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
  · exact treeEq1281

def B1279 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1280, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1279 : B1279.tree = HexagonCover.NBand.M7500_7700.SplitData.node1279 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1280
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1278 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1279, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1278 : B1278.tree = HexagonCover.NBand.M7500_7700.SplitData.node1278 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1279
  · rfl

def B1277 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1278, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1277 : B1277.tree = HexagonCover.NBand.M7500_7700.SplitData.node1277 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1278
  · rfl
  · rfl

def B1270 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1271, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1277]
theorem treeEq1270 : B1270.tree = HexagonCover.NBand.M7500_7700.SplitData.node1270 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1271
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1277

def B1287 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1287 : B1287.tree = HexagonCover.NBand.M7500_7700.SplitData.node1287 := by
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

def B1286 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1287]
theorem treeEq1286 : B1286.tree = HexagonCover.NBand.M7500_7700.SplitData.node1286 := by
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
  · exact treeEq1287

def B1285 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1286, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1285 : B1285.tree = HexagonCover.NBand.M7500_7700.SplitData.node1285 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1286
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1284 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1285, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1284 : B1284.tree = HexagonCover.NBand.M7500_7700.SplitData.node1284 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1285
  · rfl

def B1283 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1284, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1283 : B1283.tree = HexagonCover.NBand.M7500_7700.SplitData.node1283 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1284
  · rfl
  · rfl

def B1269 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1270, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1283]
theorem treeEq1269 : B1269.tree = HexagonCover.NBand.M7500_7700.SplitData.node1269 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1270
  · rfl
  · rfl
  · rfl
  · exact treeEq1283

def B1249 : Block := .branch 74 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip1249_1250, B1269, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq1249 : B1249.tree = HexagonCover.NBand.M7500_7700.SplitData.node1249 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1269
  · rfl
  · rfl
  · rfl

theorem accepted1249 : B1249.accepted = true := by decide +kernel
theorem checked1249 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1249 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1249]
  exact B1249.sound accepted1249
#print axioms checked1249

def Tip1288_1289 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1289 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1289
def B1315 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1315 : B1315.tree = HexagonCover.NBand.M7500_7700.SplitData.node1315 := by
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

def B1314 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1315]
theorem treeEq1314 : B1314.tree = HexagonCover.NBand.M7500_7700.SplitData.node1314 := by
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
  · exact treeEq1315

def B1313 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1314, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1313 : B1313.tree = HexagonCover.NBand.M7500_7700.SplitData.node1313 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1314
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1312 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1313, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1312 : B1312.tree = HexagonCover.NBand.M7500_7700.SplitData.node1312 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1313
  · rfl

def B1311 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1312, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1311 : B1311.tree = HexagonCover.NBand.M7500_7700.SplitData.node1311 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1312
  · rfl
  · rfl

def B1310 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1311]
theorem treeEq1310 : B1310.tree = HexagonCover.NBand.M7500_7700.SplitData.node1310 := by
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
  · exact treeEq1311

def B1321 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1321 : B1321.tree = HexagonCover.NBand.M7500_7700.SplitData.node1321 := by
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

def B1320 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1321, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1320 : B1320.tree = HexagonCover.NBand.M7500_7700.SplitData.node1320 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1321
  · rfl
  · rfl

def B1319 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1320]
theorem treeEq1319 : B1319.tree = HexagonCover.NBand.M7500_7700.SplitData.node1319 := by
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
  · exact treeEq1320

def B1318 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1319, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1318 : B1318.tree = HexagonCover.NBand.M7500_7700.SplitData.node1318 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1319
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1317 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1318, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1317 : B1317.tree = HexagonCover.NBand.M7500_7700.SplitData.node1317 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1318
  · rfl

def B1316 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1317, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1316 : B1316.tree = HexagonCover.NBand.M7500_7700.SplitData.node1316 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1317
  · rfl
  · rfl

def B1309 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1310, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1316]
theorem treeEq1309 : B1309.tree = HexagonCover.NBand.M7500_7700.SplitData.node1309 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1310
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1316

def B1326 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1326 : B1326.tree = HexagonCover.NBand.M7500_7700.SplitData.node1326 := by
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

def B1325 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1326]
theorem treeEq1325 : B1325.tree = HexagonCover.NBand.M7500_7700.SplitData.node1325 := by
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
  · exact treeEq1326

def B1324 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1325, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1324 : B1324.tree = HexagonCover.NBand.M7500_7700.SplitData.node1324 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1325
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1323 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1324, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1323 : B1323.tree = HexagonCover.NBand.M7500_7700.SplitData.node1323 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1324
  · rfl

def B1322 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1323, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1322 : B1322.tree = HexagonCover.NBand.M7500_7700.SplitData.node1322 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1323
  · rfl
  · rfl

def B1308 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1309, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1322]
theorem treeEq1308 : B1308.tree = HexagonCover.NBand.M7500_7700.SplitData.node1308 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1309
  · rfl
  · rfl
  · rfl
  · exact treeEq1322

def B1288 : Block := .branch 74 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip1288_1289, B1308, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq1288 : B1288.tree = HexagonCover.NBand.M7500_7700.SplitData.node1288 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1308
  · rfl
  · rfl
  · rfl

theorem accepted1288 : B1288.accepted = true := by decide +kernel
theorem checked1288 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1288 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1288]
  exact B1288.sound accepted1288
#print axioms checked1288

end HexagonCover.NBand.M7500_7700.SplitTree.Run0016
