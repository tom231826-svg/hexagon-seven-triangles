import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0015
import HexagonCover.NBand.M7500_7700.SplitTree.Run0016
import HexagonCover.NBand.M7500_7700.SplitTree.Run0017
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0018
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1242_1249 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1249 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0016.checked1249
def Tip1242_1288 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1288 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0016.checked1288
def Tip1242_1328 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1328 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0017.checked1328
def Tip1242_1367 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1367 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0017.checked1367
def B1248 : Block := .branch 73 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip1242_1249, Tip1242_1288, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq1248 : B1248.tree = HexagonCover.NBand.M7500_7700.SplitData.node1248 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1327 : Block := .branch 73 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip1242_1328, Tip1242_1367, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq1327 : B1327.tree = HexagonCover.NBand.M7500_7700.SplitData.node1327 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1247 : Block := .branch 72 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), B1248, B1327, (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1247 : B1247.tree = HexagonCover.NBand.M7500_7700.SplitData.node1247 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1248
  · exact treeEq1327
  · rfl
  · rfl
  · rfl

def B1411 : Block := .branch 108 ![385, 1538, 6148, 79247505327378171660339273736, 649037107316853453566312041250832, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 910).pointIds 910), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 911).pointIds 911)]
theorem treeEq1411 : B1411.tree = HexagonCover.NBand.M7500_7700.SplitData.node1411 := by
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

def B1410 : Block := .branch 109 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664344581903655978362901889088] ![(.leaf 0 (Common.fact 904).pointIds 904), (.leaf 1 (Common.fact 905).pointIds 905), (.leaf 2 (Common.fact 906).pointIds 906), (.leaf 3 (Common.fact 907).pointIds 907), B1411, (.leaf 5 (Common.fact 908).pointIds 908), (.leaf 6 (Common.fact 909).pointIds 909)]
theorem treeEq1410 : B1410.tree = HexagonCover.NBand.M7500_7700.SplitData.node1410 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1411
  · rfl
  · rfl

def B1409 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1410]
theorem treeEq1409 : B1409.tree = HexagonCover.NBand.M7500_7700.SplitData.node1409 := by
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
  · exact treeEq1410

def B1408 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B1409, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1408 : B1408.tree = HexagonCover.NBand.M7500_7700.SplitData.node1408 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1409
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1407 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1408, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1407 : B1407.tree = HexagonCover.NBand.M7500_7700.SplitData.node1407 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1408
  · rfl

def B1406 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1407, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1406 : B1406.tree = HexagonCover.NBand.M7500_7700.SplitData.node1406 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1407
  · rfl
  · rfl

def B1246 : Block := .branch 68 ![10384593717070245552871351364092289, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), B1247, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B1406]
theorem treeEq1246 : B1246.tree = HexagonCover.NBand.M7500_7700.SplitData.node1246 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1247
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1406

def B1245 : Block := .branch 113 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1246, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1245 : B1245.tree = HexagonCover.NBand.M7500_7700.SplitData.node1245 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1246
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1244 : Block := .branch 144 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1245, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq1244 : B1244.tree = HexagonCover.NBand.M7500_7700.SplitData.node1244 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1245
  · rfl

def B1243 : Block := .branch 149 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1244, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1243 : B1243.tree = HexagonCover.NBand.M7500_7700.SplitData.node1243 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1244
  · rfl
  · rfl

def B1242 : Block := .branch 161 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B1243]
theorem treeEq1242 : B1242.tree = HexagonCover.NBand.M7500_7700.SplitData.node1242 := by
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
  · exact treeEq1243

theorem accepted1242 : B1242.accepted = true := by decide +kernel
theorem checked1242 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1242 (maskNeeds ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1242]
  exact B1242.sound accepted1242
#print axioms checked1242

def Tip1035_1158 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1158 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0015.checked1158
def Tip1035_1197 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1197 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0015.checked1197
def Tip1035_1037 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1037 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0015.checked1037
def Tip1035_1242 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1242 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] checked1242
def B1157 : Block := .branch 73 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip1035_1158, Tip1035_1197, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq1157 : B1157.tree = HexagonCover.NBand.M7500_7700.SplitData.node1157 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1241 : Block := .branch 108 ![385, 1538, 6148, 79247505327378171660339273736, 649037107316853453566312041250832, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 910).pointIds 910), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 911).pointIds 911)]
theorem treeEq1241 : B1241.tree = HexagonCover.NBand.M7500_7700.SplitData.node1241 := by
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

def B1240 : Block := .branch 109 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664344581903655978362901889088] ![(.leaf 0 (Common.fact 904).pointIds 904), (.leaf 1 (Common.fact 905).pointIds 905), (.leaf 2 (Common.fact 906).pointIds 906), (.leaf 3 (Common.fact 907).pointIds 907), B1241, (.leaf 5 (Common.fact 908).pointIds 908), (.leaf 6 (Common.fact 909).pointIds 909)]
theorem treeEq1240 : B1240.tree = HexagonCover.NBand.M7500_7700.SplitData.node1240 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1241
  · rfl
  · rfl

def B1239 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 79247505327378171660339273736, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1240]
theorem treeEq1239 : B1239.tree = HexagonCover.NBand.M7500_7700.SplitData.node1239 := by
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
  · exact treeEq1240

def B1238 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B1239, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1238 : B1238.tree = HexagonCover.NBand.M7500_7700.SplitData.node1238 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1239
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1237 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1238, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1237 : B1237.tree = HexagonCover.NBand.M7500_7700.SplitData.node1237 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1238
  · rfl

def B1236 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1237, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1236 : B1236.tree = HexagonCover.NBand.M7500_7700.SplitData.node1236 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1237
  · rfl
  · rfl

def B1156 : Block := .branch 68 ![10384593717070245552871351364092289, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), B1157, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B1236]
theorem treeEq1156 : B1156.tree = HexagonCover.NBand.M7500_7700.SplitData.node1156 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1157
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1236

def B1155 : Block := .branch 113 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1156, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1155 : B1155.tree = HexagonCover.NBand.M7500_7700.SplitData.node1155 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1156
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1154 : Block := .branch 144 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1155, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq1154 : B1154.tree = HexagonCover.NBand.M7500_7700.SplitData.node1154 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1155
  · rfl

def B1153 : Block := .branch 149 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1154, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1153 : B1153.tree = HexagonCover.NBand.M7500_7700.SplitData.node1153 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1154
  · rfl
  · rfl

def B1152 : Block := .branch 161 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 854).pointIds 854), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B1153]
theorem treeEq1152 : B1152.tree = HexagonCover.NBand.M7500_7700.SplitData.node1152 := by
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
  · exact treeEq1153

def B1036 : Block := .branch 72 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), Tip1035_1037, B1152, (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1036 : B1036.tree = HexagonCover.NBand.M7500_7700.SplitData.node1036 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1152
  · rfl
  · rfl
  · rfl

def B1035 : Block := .branch 71 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 348).pointIds 348), (.leaf 1 (Common.fact 349).pointIds 349), B1036, Tip1035_1242, (.leaf 4 (Common.fact 350).pointIds 350), (.leaf 5 (Common.fact 351).pointIds 351), (.leaf 0 [] 0)]
theorem treeEq1035 : B1035.tree = HexagonCover.NBand.M7500_7700.SplitData.node1035 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1036
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1035 : B1035.accepted = true := by decide +kernel
theorem checked1035 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1035 (maskNeeds ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1035]
  exact B1035.sound accepted1035
#print axioms checked1035

def Tip1033_1035 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1035 ![590295810358705652097, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] checked1035
def B1419 : Block := .branch 132 ![385, 1538, 6148, 24584, 5986493394212044715827068535409984783888156687695888, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 919).pointIds 919), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1419 : B1419.tree = HexagonCover.NBand.M7500_7700.SplitData.node1419 := by
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

def B1418 : Block := .branch 157 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2865645758011185073687339798035314453518876704, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1419, (.leaf 5 (Common.fact 918).pointIds 918), (.leaf 0 [] 0)]
theorem treeEq1418 : B1418.tree = HexagonCover.NBand.M7500_7700.SplitData.node1418 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1419
  · rfl
  · rfl

def B1417 : Block := .branch 143 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 916).pointIds 916), B1418, (.leaf 6 (Common.fact 917).pointIds 917)]
theorem treeEq1417 : B1417.tree = HexagonCover.NBand.M7500_7700.SplitData.node1417 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1418
  · rfl

def B1416 : Block := .branch 125 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 2854495385411919762116571938898990272765886496, 21778071483257129054808238709450164666432] ![B1417, (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 915).pointIds 915)]
theorem treeEq1416 : B1416.tree = HexagonCover.NBand.M7500_7700.SplitData.node1416 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1417
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1415 : Block := .branch 151 ![385, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1416, (.leaf 6 (Common.fact 914).pointIds 914)]
theorem treeEq1415 : B1415.tree = HexagonCover.NBand.M7500_7700.SplitData.node1415 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1416
  · rfl

def B1414 : Block := .branch 170 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 21778071483257129054808238709450164666432] ![B1415, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 913).pointIds 913)]
theorem treeEq1414 : B1414.tree = HexagonCover.NBand.M7500_7700.SplitData.node1414 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1415
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1413 : Block := .branch 171 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1414, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1413 : B1413.tree = HexagonCover.NBand.M7500_7700.SplitData.node1413 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1414
  · rfl

def B1412 : Block := .branch 172 ![385, 144115188075857410, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1413, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 912).pointIds 912)]
theorem treeEq1412 : B1412.tree = HexagonCover.NBand.M7500_7700.SplitData.node1412 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1413
  · rfl
  · rfl

def B1034 : Block := .branch 69 ![385, 147790125371790198274, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![Tip1033_1035, (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 450).pointIds 450), (.leaf 4 (Common.fact 451).pointIds 451), (.leaf 5 (Common.fact 452).pointIds 452), B1412]
theorem treeEq1034 : B1034.tree = HexagonCover.NBand.M7500_7700.SplitData.node1034 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1412

def B1425 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129658828426658995722780736] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 111).pointIds 111), (.leaf 6 (Common.fact 924).pointIds 924)]
theorem treeEq1425 : B1425.tree = HexagonCover.NBand.M7500_7700.SplitData.node1425 := by
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

def B1424 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129658828426658995722780736] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1425, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 922).pointIds 922)]
theorem treeEq1424 : B1424.tree = HexagonCover.NBand.M7500_7700.SplitData.node1424 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1425
  · rfl
  · rfl

def B1423 : Block := .branch 79 ![1496577676626844588240573268701473812127674924007809, 216172782113785346, 6148, 24584, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1424]
theorem treeEq1423 : B1423.tree = HexagonCover.NBand.M7500_7700.SplitData.node1423 := by
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
  · exact treeEq1424

def B1422 : Block := .branch 170 ![385, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 21778071483257129054365516851681135427648] ![B1423, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 921).pointIds 921)]
theorem treeEq1422 : B1422.tree = HexagonCover.NBand.M7500_7700.SplitData.node1422 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1423
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1421 : Block := .branch 171 ![385, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1422, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1421 : B1421.tree = HexagonCover.NBand.M7500_7700.SplitData.node1421 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1422
  · rfl

def B1420 : Block := .branch 172 ![385, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1421, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq1420 : B1420.tree = HexagonCover.NBand.M7500_7700.SplitData.node1420 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1421
  · rfl
  · rfl

def B1033 : Block := .branch 67 ![385, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 233).pointIds 233), B1034, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), B1420]
theorem treeEq1033 : B1033.tree = HexagonCover.NBand.M7500_7700.SplitData.node1033 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1034
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1420

theorem accepted1033 : B1033.accepted = true := by decide +kernel
theorem checked1033 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1033 (maskNeeds ![385, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1033]
  exact B1033.sound accepted1033
#print axioms checked1033

def B1490 : Block := .branch 124 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 98320, 393248, 11869048958202650982480078096588602233847872] ![(.leaf 0 (Common.fact 465).pointIds 465), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1490 : B1490.tree = HexagonCover.NBand.M7500_7700.SplitData.node1490 := by
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

def B1489 : Block := .branch 143 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 893).pointIds 893), (.leaf 5 (Common.fact 569).pointIds 569), B1490]
theorem treeEq1489 : B1489.tree = HexagonCover.NBand.M7500_7700.SplitData.node1489 := by
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
  · exact treeEq1490

def B1488 : Block := .branch 100 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![B1489, (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq1488 : B1488.tree = HexagonCover.NBand.M7500_7700.SplitData.node1488 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1489
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1487 : Block := .branch 112 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![B1488, (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), (.leaf 6 (Common.fact 888).pointIds 888)]
theorem treeEq1487 : B1487.tree = HexagonCover.NBand.M7500_7700.SplitData.node1487 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1488
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1486 : Block := .branch 113 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![B1487, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq1486 : B1486.tree = HexagonCover.NBand.M7500_7700.SplitData.node1486 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1487
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1485 : Block := .branch 128 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B1486, (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq1485 : B1485.tree = HexagonCover.NBand.M7500_7700.SplitData.node1485 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1486
  · rfl
  · rfl
  · rfl

def B1484 : Block := .branch 168 ![748288838313422294120286634955199815871152049357185, 1461501637330902918204303802735925709793382106626, 18446884811197913092, 38685626227668133590622216, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707231499229770367501933528202494029468270656] ![B1485, (.leaf 1 (Common.fact 490).pointIds 490), (.leaf 2 (Common.fact 884).pointIds 884), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq1484 : B1484.tree = HexagonCover.NBand.M7500_7700.SplitData.node1484 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1485
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1483 : Block := .branch 160 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 18446884811197913092, 38685626227668133590622216, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707231499229770367501933528202494029468270656] ![(.leaf 0 (Common.fact 362).pointIds 362), B1484, (.leaf 2 (Common.fact 883).pointIds 883), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1483 : B1483.tree = HexagonCover.NBand.M7500_7700.SplitData.node1483 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1484
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1482 : Block := .branch 162 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 18446884811197913092, 38685626227668133590622216, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707231499229770367501933528202494029468270656] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B1483, (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1482 : B1482.tree = HexagonCover.NBand.M7500_7700.SplitData.node1482 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1483
  · rfl
  · rfl
  · rfl

def B1481 : Block := .branch 139 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 18446884811197913092, 79266848140492005727134572552, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310706534600942316285528760537006473768171208768] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B1482]
theorem treeEq1481 : B1481.tree = HexagonCover.NBand.M7500_7700.SplitData.node1481 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1482

def B1480 : Block := .branch 151 ![748288838313422294120286634955199815871152049357185, 618970019642690137449563650, 18446884811197913092, 79266848140492005727134572552, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310706534600942316285528760537006473768171208768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B1481, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 880).pointIds 880)]
theorem treeEq1480 : B1480.tree = HexagonCover.NBand.M7500_7700.SplitData.node1480 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1481
  · rfl
  · rfl

def B1479 : Block := .branch 172 ![748288838313422294120286634955199815871152049357185, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), (.leaf 4 (Common.fact 878).pointIds 878), (.leaf 5 (Common.fact 879).pointIds 879), B1480]
theorem treeEq1479 : B1479.tree = HexagonCover.NBand.M7500_7700.SplitData.node1479 := by
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
  · exact treeEq1480

def B1478 : Block := .branch 171 ![748288838313422294120286634955199815871152049357185, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), B1479, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1478 : B1478.tree = HexagonCover.NBand.M7500_7700.SplitData.node1478 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1479
  · rfl
  · rfl

def B1477 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), B1478, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1477 : B1477.tree = HexagonCover.NBand.M7500_7700.SplitData.node1477 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1478
  · rfl

def B1476 : Block := .branch 79 ![748288838313422294120286634350736906063837462004097, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B1477, (.leaf 1 (Common.fact 939).pointIds 939), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq1476 : B1476.tree = HexagonCover.NBand.M7500_7700.SplitData.node1476 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1477
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1475 : Block := .branch 169 ![385, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B1476, (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq1475 : B1475.tree = HexagonCover.NBand.M7500_7700.SplitData.node1475 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1476
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1474 : Block := .branch 132 ![385, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B1475]
theorem treeEq1474 : B1474.tree = HexagonCover.NBand.M7500_7700.SplitData.node1474 := by
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
  · exact treeEq1475

def B1473 : Block := .branch 133 ![385, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B1474]
theorem treeEq1473 : B1473.tree = HexagonCover.NBand.M7500_7700.SplitData.node1473 := by
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
  · exact treeEq1474

def B1472 : Block := .branch 157 ![385, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1473, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq1472 : B1472.tree = HexagonCover.NBand.M7500_7700.SplitData.node1472 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1473
  · rfl
  · rfl

def B1471 : Block := .branch 125 ![590295810358705652097, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B1472, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq1471 : B1471.tree = HexagonCover.NBand.M7500_7700.SplitData.node1471 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1472
  · rfl

theorem accepted1471 : B1471.accepted = true := by decide +kernel
theorem checked1471 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1471 (maskNeeds ![590295810358705652097, 618970019786805325525419522, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1471]
  exact B1471.sound accepted1471
#print axioms checked1471

end HexagonCover.NBand.M7500_7700.SplitTree.Run0018
