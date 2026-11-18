import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0016
import HexagonCover.NBand.M6667_6700.SplitTree.Run0020
import HexagonCover.NBand.M6667_6700.SplitTree.Run0021
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0022
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1514_1530 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1530 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0021.checked1530
def Tip1514_1593 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1593 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] HexagonCover.NBand.M6667_6700.SplitTree.Run0021.checked1593
def B1517 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1517 : B1517.tree = HexagonCover.NBand.M6667_6700.SplitData.node1517 := by
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

def B1516 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1517]
theorem treeEq1516 : B1516.tree = HexagonCover.NBand.M6667_6700.SplitData.node1516 := by
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
  · exact treeEq1517

def B1521 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq1521 : B1521.tree = HexagonCover.NBand.M6667_6700.SplitData.node1521 := by
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

def B1520 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B1521]
theorem treeEq1520 : B1520.tree = HexagonCover.NBand.M6667_6700.SplitData.node1520 := by
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
  · exact treeEq1521

def B1524 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq1524 : B1524.tree = HexagonCover.NBand.M6667_6700.SplitData.node1524 := by
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

def B1523 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B1524]
theorem treeEq1523 : B1523.tree = HexagonCover.NBand.M6667_6700.SplitData.node1523 := by
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
  · exact treeEq1524

def B1529 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq1529 : B1529.tree = HexagonCover.NBand.M6667_6700.SplitData.node1529 := by
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

def B1528 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1529, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq1528 : B1528.tree = HexagonCover.NBand.M6667_6700.SplitData.node1528 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1529
  · rfl
  · rfl

def B1527 : Block := .branch 158 ![5319508131568930906582414993892835713, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1528]
theorem treeEq1527 : B1527.tree = HexagonCover.NBand.M6667_6700.SplitData.node1527 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1528

def B1526 : Block := .branch 163 ![5319508131568930906582414993892835713, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B1527]
theorem treeEq1526 : B1526.tree = HexagonCover.NBand.M6667_6700.SplitData.node1526 := by
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
  · exact treeEq1527

def B1525 : Block := .branch 122 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B1526, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip1514_1530]
theorem treeEq1525 : B1525.tree = HexagonCover.NBand.M6667_6700.SplitData.node1525 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1526
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1522 : Block := .branch 121 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664091495163138109364451942813045360164928] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B1523, (.leaf 5 (Common.fact 430).pointIds 430), B1525]
theorem treeEq1522 : B1522.tree = HexagonCover.NBand.M6667_6700.SplitData.node1522 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1523
  · rfl
  · exact treeEq1525

def B1519 : Block := .branch 120 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B1520, (.leaf 5 (Common.fact 163).pointIds 163), B1522]
theorem treeEq1519 : B1519.tree = HexagonCover.NBand.M6667_6700.SplitData.node1519 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1520
  · rfl
  · exact treeEq1522

def B1518 : Block := .branch 140 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1519, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq1518 : B1518.tree = HexagonCover.NBand.M6667_6700.SplitData.node1518 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1519
  · rfl
  · rfl

def B1515 : Block := .branch 119 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1516, (.leaf 5 (Common.fact 419).pointIds 419), B1518]
theorem treeEq1515 : B1515.tree = HexagonCover.NBand.M6667_6700.SplitData.node1515 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1516
  · rfl
  · exact treeEq1518

def B1514 : Block := .branch 111 ![1152921504606847361, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B1515, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip1514_1593]
theorem treeEq1514 : B1514.tree = HexagonCover.NBand.M6667_6700.SplitData.node1514 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1515
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1514 : B1514.accepted = true := by decide +kernel
theorem checked1514 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1514 (maskNeeds ![1152921504606847361, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320]) := by
  rw [← treeEq1514]
  exact B1514.sound accepted1514
#print axioms checked1514

def Tip1206_1222 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1222 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] HexagonCover.NBand.M6667_6700.SplitTree.Run0020.checked1222
def Tip1206_1494 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1494 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] HexagonCover.NBand.M6667_6700.SplitTree.Run0020.checked1494
def Tip1206_1514 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1514 ![1152921504606847361, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] checked1514
def B1209 : Block := .branch 132 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764357729643384042495148096] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq1209 : B1209.tree = HexagonCover.NBand.M6667_6700.SplitData.node1209 := by
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

def B1208 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 324518553658426726783156020674576, 393248, 6360455125664089500023387130006992737320205033144384] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B1209]
theorem treeEq1208 : B1208.tree = HexagonCover.NBand.M6667_6700.SplitData.node1208 := by
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
  · exact treeEq1209

def B1214 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1214 : B1214.tree = HexagonCover.NBand.M6667_6700.SplitData.node1214 := by
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

def B1213 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1214]
theorem treeEq1213 : B1213.tree = HexagonCover.NBand.M6667_6700.SplitData.node1213 := by
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
  · exact treeEq1214

def B1218 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq1218 : B1218.tree = HexagonCover.NBand.M6667_6700.SplitData.node1218 := by
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

def B1217 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B1218]
theorem treeEq1217 : B1217.tree = HexagonCover.NBand.M6667_6700.SplitData.node1217 := by
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
  · exact treeEq1218

def B1221 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq1221 : B1221.tree = HexagonCover.NBand.M6667_6700.SplitData.node1221 := by
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

def B1220 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B1221]
theorem treeEq1220 : B1220.tree = HexagonCover.NBand.M6667_6700.SplitData.node1220 := by
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
  · exact treeEq1221

def B1219 : Block := .branch 121 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664091495163455022014509000163419535966272] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B1220, (.leaf 5 (Common.fact 430).pointIds 430), Tip1206_1222]
theorem treeEq1219 : B1219.tree = HexagonCover.NBand.M6667_6700.SplitData.node1219 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1220
  · rfl
  · rfl

def B1216 : Block := .branch 120 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B1217, (.leaf 5 (Common.fact 163).pointIds 163), B1219]
theorem treeEq1216 : B1216.tree = HexagonCover.NBand.M6667_6700.SplitData.node1216 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1217
  · rfl
  · exact treeEq1219

def B1215 : Block := .branch 140 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1216, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq1215 : B1215.tree = HexagonCover.NBand.M6667_6700.SplitData.node1215 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1216
  · rfl
  · rfl

def B1212 : Block := .branch 119 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1213, (.leaf 5 (Common.fact 419).pointIds 419), B1215]
theorem treeEq1212 : B1212.tree = HexagonCover.NBand.M6667_6700.SplitData.node1212 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1213
  · rfl
  · exact treeEq1215

def B1211 : Block := .branch 111 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![B1212, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip1206_1494]
theorem treeEq1211 : B1211.tree = HexagonCover.NBand.M6667_6700.SplitData.node1211 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1212
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1210 : Block := .branch 69 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![B1211, Tip1206_1514, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1210 : B1210.tree = HexagonCover.NBand.M6667_6700.SplitData.node1210 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1211
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1207 : Block := .branch 108 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B1208, (.leaf 5 (Common.fact 136).pointIds 136), B1210]
theorem treeEq1207 : B1207.tree = HexagonCover.NBand.M6667_6700.SplitData.node1207 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1208
  · rfl
  · exact treeEq1210

def B1615 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240258071987486287549956160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 957).pointIds 957)]
theorem treeEq1615 : B1615.tree = HexagonCover.NBand.M6667_6700.SplitData.node1615 := by
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

def B1614 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605907335081422450087952448] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1615]
theorem treeEq1614 : B1614.tree = HexagonCover.NBand.M6667_6700.SplitData.node1614 := by
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
  · exact treeEq1615

def B1613 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820541041988555074170257472] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1614, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq1613 : B1613.tree = HexagonCover.NBand.M6667_6700.SplitData.node1613 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1614
  · rfl
  · rfl

def B1206 : Block := .branch 101 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![B1207, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B1613]
theorem treeEq1206 : B1206.tree = HexagonCover.NBand.M6667_6700.SplitData.node1206 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1207
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1613

theorem accepted1206 : B1206.accepted = true := by decide +kernel
theorem checked1206 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1206 (maskNeeds ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq1206]
  exact B1206.sound accepted1206
#print axioms checked1206

def Tip1200_1206 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1206 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] checked1206
def B1618 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180749340131798850933144245764160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq1618 : B1618.tree = HexagonCover.NBand.M6667_6700.SplitData.node1618 := by
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

def B1617 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060462705781061944869306783760448] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1618]
theorem treeEq1617 : B1617.tree = HexagonCover.NBand.M6667_6700.SplitData.node1617 := by
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
  · exact treeEq1618

def B1616 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358536920414768852001930866065472] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1617, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 958).pointIds 958)]
theorem treeEq1616 : B1616.tree = HexagonCover.NBand.M6667_6700.SplitData.node1616 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1617
  · rfl
  · rfl

def B1205 : Block := .branch 91 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![Tip1200_1206, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B1616]
theorem treeEq1205 : B1205.tree = HexagonCover.NBand.M6667_6700.SplitData.node1205 := by
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
  · exact treeEq1616

def B1621 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040558027635171373431593107520] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq1621 : B1621.tree = HexagonCover.NBand.M6667_6700.SplitData.node1621 := by
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

def B1620 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923676898265309594131103808] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1621]
theorem treeEq1620 : B1620.tree = HexagonCover.NBand.M6667_6700.SplitData.node1620 := by
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
  · exact treeEq1621

def B1619 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138310605172442218213408832] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1620, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq1619 : B1619.tree = HexagonCover.NBand.M6667_6700.SplitData.node1619 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1620
  · rfl
  · rfl

def B1204 : Block := .branch 89 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 117).pointIds 117), B1205, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B1619]
theorem treeEq1204 : B1204.tree = HexagonCover.NBand.M6667_6700.SplitData.node1204 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1205
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1619

def B1624 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929078925041369935500542016] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq1624 : B1624.tree = HexagonCover.NBand.M6667_6700.SplitData.node1624 := by
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

def B1623 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294728188135306098038538304] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1624]
theorem treeEq1623 : B1623.tree = HexagonCover.NBand.M6667_6700.SplitData.node1623 := by
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
  · exact treeEq1624

def B1622 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461422011952099789096296644672] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1623, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq1622 : B1622.tree = HexagonCover.NBand.M6667_6700.SplitData.node1622 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1623
  · rfl
  · rfl

def B1203 : Block := .branch 86 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B1204, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B1622]
theorem treeEq1203 : B1203.tree = HexagonCover.NBand.M6667_6700.SplitData.node1203 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1204
  · rfl
  · rfl
  · exact treeEq1622

def B1627 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6734599544820800647083213573217930360669883178942528] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 965).pointIds 965)]
theorem treeEq1627 : B1627.tree = HexagonCover.NBand.M6667_6700.SplitData.node1627 := by
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

def B1626 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 5986310706507378352962926938867193454606045716938816] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1627]
theorem treeEq1626 : B1626.tree = HexagonCover.NBand.M6667_6700.SplitData.node1626 := by
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
  · exact treeEq1627

def B1625 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 5986310706507378354261001153500900361738669799243840] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1626, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq1625 : B1625.tree = HexagonCover.NBand.M6667_6700.SplitData.node1625 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1626
  · rfl
  · rfl

def B1202 : Block := .branch 85 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B1203, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B1625]
theorem treeEq1202 : B1202.tree = HexagonCover.NBand.M6667_6700.SplitData.node1202 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1203
  · rfl
  · rfl
  · exact treeEq1625

def B1201 : Block := .branch 137 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 997).pointIds 997), B1202, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq1201 : B1201.tree = HexagonCover.NBand.M6667_6700.SplitData.node1201 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1202
  · rfl
  · rfl

def B1200 : Block := .branch 138 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 995).pointIds 995), B1201, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq1200 : B1200.tree = HexagonCover.NBand.M6667_6700.SplitData.node1200 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1201
  · rfl
  · rfl

theorem accepted1200 : B1200.accepted = true := by decide +kernel
theorem checked1200 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1200 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464]) := by
  rw [← treeEq1200]
  exact B1200.sound accepted1200
#print axioms checked1200

def B1639 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864553951735076251741192256] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq1639 : B1639.tree = HexagonCover.NBand.M6667_6700.SplitData.node1639 := by
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

def B1638 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230203214829012414279188544] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1639]
theorem treeEq1638 : B1638.tree = HexagonCover.NBand.M6667_6700.SplitData.node1638 := by
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
  · exact treeEq1639

def B1637 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444836921736145038361493568] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1638, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq1637 : B1637.tree = HexagonCover.NBand.M6667_6700.SplitData.node1637 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1638
  · rfl
  · rfl

def B1642 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 1298074234354309339596812249989184] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq1642 : B1642.tree = HexagonCover.NBand.M6667_6700.SplitData.node1642 := by
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

def B1641 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1642, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1641 : B1641.tree = HexagonCover.NBand.M6667_6700.SplitData.node1641 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1642
  · rfl
  · rfl

def B1640 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1641, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq1640 : B1640.tree = HexagonCover.NBand.M6667_6700.SplitData.node1640 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1641
  · rfl

def B1636 : Block := .branch 84 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B1637, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B1640]
theorem treeEq1636 : B1636.tree = HexagonCover.NBand.M6667_6700.SplitData.node1636 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1637
  · rfl
  · rfl
  · exact treeEq1640

def B1645 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq1645 : B1645.tree = HexagonCover.NBand.M6667_6700.SplitData.node1645 := by
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

def B1644 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1645, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1644 : B1644.tree = HexagonCover.NBand.M6667_6700.SplitData.node1644 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1645
  · rfl
  · rfl

def B1643 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1644, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq1643 : B1643.tree = HexagonCover.NBand.M6667_6700.SplitData.node1643 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1644
  · rfl

def B1635 : Block := .branch 80 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![B1636, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B1643]
theorem treeEq1635 : B1635.tree = HexagonCover.NBand.M6667_6700.SplitData.node1635 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1636
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1643

def B1634 : Block := .branch 95 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), B1635, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq1634 : B1634.tree = HexagonCover.NBand.M6667_6700.SplitData.node1634 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1635
  · rfl
  · rfl
  · rfl

theorem accepted1634 : B1634.accepted = true := by decide +kernel
theorem checked1634 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1634 (maskNeeds ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952]) := by
  rw [← treeEq1634]
  exact B1634.sound accepted1634
#print axioms checked1634

def Tip0909_0913 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0913 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0016.checked0913
def Tip0909_1185 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1185 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] HexagonCover.NBand.M6667_6700.SplitTree.Run0016.checked1185
def B0912 : Block := .branch 138 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 995).pointIds 995), Tip0909_0913, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq0912 : B0912.tree = HexagonCover.NBand.M6667_6700.SplitData.node0912 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1179 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1044).pointIds 1044)]
theorem treeEq1179 : B1179.tree = HexagonCover.NBand.M6667_6700.SplitData.node1179 := by
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

def B1178 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1179, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1043).pointIds 1043)]
theorem treeEq1178 : B1178.tree = HexagonCover.NBand.M6667_6700.SplitData.node1178 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1179
  · rfl
  · rfl

def B1177 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1178, (.leaf 6 (Common.fact 1042).pointIds 1042)]
theorem treeEq1177 : B1177.tree = HexagonCover.NBand.M6667_6700.SplitData.node1177 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1178
  · rfl

def B0911 : Block := .branch 84 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B0912, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B1177]
theorem treeEq0911 : B0911.tree = HexagonCover.NBand.M6667_6700.SplitData.node0911 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0912
  · rfl
  · rfl
  · exact treeEq1177

def B1184 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1049).pointIds 1049)]
theorem treeEq1184 : B1184.tree = HexagonCover.NBand.M6667_6700.SplitData.node1184 := by
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

def B1183 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156713806814526015499804044744216479793216] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1184, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1048).pointIds 1048)]
theorem treeEq1183 : B1183.tree = HexagonCover.NBand.M6667_6700.SplitData.node1183 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1184
  · rfl
  · rfl

def B1182 : Block := .branch 121 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 460).pointIds 460), (.leaf 5 (Common.fact 430).pointIds 430), B1183]
theorem treeEq1182 : B1182.tree = HexagonCover.NBand.M6667_6700.SplitData.node1182 := by
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
  · exact treeEq1183

def B1181 : Block := .branch 149 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B1182, (.leaf 5 (Common.fact 1046).pointIds 1046), (.leaf 6 (Common.fact 1047).pointIds 1047)]
theorem treeEq1181 : B1181.tree = HexagonCover.NBand.M6667_6700.SplitData.node1181 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1182
  · rfl
  · rfl

def B1180 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1181, (.leaf 6 (Common.fact 1045).pointIds 1045)]
theorem treeEq1180 : B1180.tree = HexagonCover.NBand.M6667_6700.SplitData.node1180 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1181
  · rfl

def B0910 : Block := .branch 80 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![B0911, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B1180]
theorem treeEq0910 : B0910.tree = HexagonCover.NBand.M6667_6700.SplitData.node0910 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0911
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1180

def B0909 : Block := .branch 78 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 87).pointIds 87), B0910, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip0909_1185]
theorem treeEq0909 : B0909.tree = HexagonCover.NBand.M6667_6700.SplitData.node0909 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0910
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0909 : B0909.accepted = true := by decide +kernel
theorem checked0909 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0909 (maskNeeds ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq0909]
  exact B0909.sound accepted0909
#print axioms checked0909

end HexagonCover.NBand.M6667_6700.SplitTree.Run0022
