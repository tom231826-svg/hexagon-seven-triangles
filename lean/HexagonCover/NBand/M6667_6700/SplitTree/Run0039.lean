import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0035
import HexagonCover.NBand.M6667_6700.SplitTree.Run0036
import HexagonCover.NBand.M6667_6700.SplitTree.Run0038
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0039
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2652_2669 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2669 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0036.checked2669
def Tip2652_2732 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2732 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] HexagonCover.NBand.M6667_6700.SplitTree.Run0038.checked2732
def Tip2652_2875 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2875 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] HexagonCover.NBand.M6667_6700.SplitTree.Run0038.checked2875
def B2655 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq2655 : B2655.tree = HexagonCover.NBand.M6667_6700.SplitData.node2655 := by
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

def B2654 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2655]
theorem treeEq2654 : B2654.tree = HexagonCover.NBand.M6667_6700.SplitData.node2654 := by
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
  · exact treeEq2655

def B2660 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2660 : B2660.tree = HexagonCover.NBand.M6667_6700.SplitData.node2660 := by
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

def B2659 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B2660]
theorem treeEq2659 : B2659.tree = HexagonCover.NBand.M6667_6700.SplitData.node2659 := by
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
  · exact treeEq2660

def B2663 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq2663 : B2663.tree = HexagonCover.NBand.M6667_6700.SplitData.node2663 := by
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

def B2662 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B2663]
theorem treeEq2662 : B2662.tree = HexagonCover.NBand.M6667_6700.SplitData.node2662 := by
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
  · exact treeEq2663

def B2668 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq2668 : B2668.tree = HexagonCover.NBand.M6667_6700.SplitData.node2668 := by
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

def B2667 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2668, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2667 : B2667.tree = HexagonCover.NBand.M6667_6700.SplitData.node2667 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2668
  · rfl
  · rfl

def B2666 : Block := .branch 158 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 1190).pointIds 1190), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2667]
theorem treeEq2666 : B2666.tree = HexagonCover.NBand.M6667_6700.SplitData.node2666 := by
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
  · exact treeEq2667

def B2665 : Block := .branch 163 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 1189).pointIds 1189), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2666]
theorem treeEq2665 : B2665.tree = HexagonCover.NBand.M6667_6700.SplitData.node2665 := by
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
  · exact treeEq2666

def B2664 : Block := .branch 122 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B2665, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip2652_2669]
theorem treeEq2664 : B2664.tree = HexagonCover.NBand.M6667_6700.SplitData.node2664 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2665
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2661 : Block := .branch 121 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664091495163138109364451942813045360164928] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B2662, (.leaf 5 (Common.fact 430).pointIds 430), B2664]
theorem treeEq2661 : B2661.tree = HexagonCover.NBand.M6667_6700.SplitData.node2661 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2662
  · rfl
  · exact treeEq2664

def B2658 : Block := .branch 120 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B2659, (.leaf 5 (Common.fact 163).pointIds 163), B2661]
theorem treeEq2658 : B2658.tree = HexagonCover.NBand.M6667_6700.SplitData.node2658 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2659
  · rfl
  · exact treeEq2661

def B2657 : Block := .branch 79 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![B2658, Tip2652_2732, (.leaf 2 (Common.fact 1184).pointIds 1184), (.leaf 3 (Common.fact 1185).pointIds 1185), (.leaf 4 (Common.fact 1186).pointIds 1186), (.leaf 5 (Common.fact 1187).pointIds 1187), (.leaf 6 (Common.fact 1201).pointIds 1201)]
theorem treeEq2657 : B2657.tree = HexagonCover.NBand.M6667_6700.SplitData.node2657 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2658
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2656 : Block := .branch 140 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2657, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2656 : B2656.tree = HexagonCover.NBand.M6667_6700.SplitData.node2656 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2657
  · rfl
  · rfl

def B2653 : Block := .branch 119 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2654, (.leaf 5 (Common.fact 419).pointIds 419), B2656]
theorem treeEq2653 : B2653.tree = HexagonCover.NBand.M6667_6700.SplitData.node2653 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2654
  · rfl
  · exact treeEq2656

def B2652 : Block := .branch 111 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B2653, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip2652_2875]
theorem treeEq2652 : B2652.tree = HexagonCover.NBand.M6667_6700.SplitData.node2652 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2653
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2652 : B2652.accepted = true := by decide +kernel
theorem checked2652 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2652 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320]) := by
  rw [← treeEq2652]
  exact B2652.sound accepted2652
#print axioms checked2652

def Tip2549_2569 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2569 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0035.checked2569
def Tip2549_2632 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2632 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] HexagonCover.NBand.M6667_6700.SplitTree.Run0035.checked2632
def Tip2549_2652 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2652 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] checked2652
def B2551 : Block := .branch 132 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764357729643384042495148096] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq2551 : B2551.tree = HexagonCover.NBand.M6667_6700.SplitData.node2551 := by
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

def B2550 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387130006992737320205033144384] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B2551]
theorem treeEq2550 : B2550.tree = HexagonCover.NBand.M6667_6700.SplitData.node2550 := by
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
  · exact treeEq2551

def B2556 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq2556 : B2556.tree = HexagonCover.NBand.M6667_6700.SplitData.node2556 := by
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

def B2555 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2556]
theorem treeEq2555 : B2555.tree = HexagonCover.NBand.M6667_6700.SplitData.node2555 := by
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
  · exact treeEq2556

def B2560 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2560 : B2560.tree = HexagonCover.NBand.M6667_6700.SplitData.node2560 := by
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

def B2559 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B2560]
theorem treeEq2559 : B2559.tree = HexagonCover.NBand.M6667_6700.SplitData.node2559 := by
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
  · exact treeEq2560

def B2563 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq2563 : B2563.tree = HexagonCover.NBand.M6667_6700.SplitData.node2563 := by
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

def B2562 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B2563]
theorem treeEq2562 : B2562.tree = HexagonCover.NBand.M6667_6700.SplitData.node2562 := by
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
  · exact treeEq2563

def B2568 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq2568 : B2568.tree = HexagonCover.NBand.M6667_6700.SplitData.node2568 := by
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

def B2567 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2568, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2567 : B2567.tree = HexagonCover.NBand.M6667_6700.SplitData.node2567 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2568
  · rfl
  · rfl

def B2566 : Block := .branch 158 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 1181).pointIds 1181), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2567]
theorem treeEq2566 : B2566.tree = HexagonCover.NBand.M6667_6700.SplitData.node2566 := by
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
  · exact treeEq2567

def B2565 : Block := .branch 163 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 1180).pointIds 1180), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2566]
theorem treeEq2565 : B2565.tree = HexagonCover.NBand.M6667_6700.SplitData.node2565 := by
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
  · exact treeEq2566

def B2564 : Block := .branch 122 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B2565, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip2549_2569]
theorem treeEq2564 : B2564.tree = HexagonCover.NBand.M6667_6700.SplitData.node2564 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2565
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2561 : Block := .branch 121 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664091495163138109364451942813045360164928] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B2562, (.leaf 5 (Common.fact 430).pointIds 430), B2564]
theorem treeEq2561 : B2561.tree = HexagonCover.NBand.M6667_6700.SplitData.node2561 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2562
  · rfl
  · exact treeEq2564

def B2558 : Block := .branch 120 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B2559, (.leaf 5 (Common.fact 163).pointIds 163), B2561]
theorem treeEq2558 : B2558.tree = HexagonCover.NBand.M6667_6700.SplitData.node2558 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2559
  · rfl
  · exact treeEq2561

def B2557 : Block := .branch 140 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2558, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2557 : B2557.tree = HexagonCover.NBand.M6667_6700.SplitData.node2557 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2558
  · rfl
  · rfl

def B2554 : Block := .branch 119 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2555, (.leaf 5 (Common.fact 419).pointIds 419), B2557]
theorem treeEq2554 : B2554.tree = HexagonCover.NBand.M6667_6700.SplitData.node2554 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2555
  · rfl
  · exact treeEq2557

def B2553 : Block := .branch 111 ![590295810358705652097, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B2554, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip2549_2632]
theorem treeEq2553 : B2553.tree = HexagonCover.NBand.M6667_6700.SplitData.node2553 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2554
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2552 : Block := .branch 69 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B2553, Tip2549_2652, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq2552 : B2552.tree = HexagonCover.NBand.M6667_6700.SplitData.node2552 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2553
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2549 : Block := .branch 108 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B2550, (.leaf 5 (Common.fact 136).pointIds 136), B2552]
theorem treeEq2549 : B2549.tree = HexagonCover.NBand.M6667_6700.SplitData.node2549 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2550
  · rfl
  · exact treeEq2552

theorem accepted2549 : B2549.accepted = true := by decide +kernel
theorem checked2549 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2549 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq2549]
  exact B2549.sound accepted2549
#print axioms checked2549

def Tip2544_2549 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2549 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501321461344640699644452829115449408] checked2549
def B2897 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240258071987486287549956160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 957).pointIds 957)]
theorem treeEq2897 : B2897.tree = HexagonCover.NBand.M6667_6700.SplitData.node2897 := by
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

def B2896 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605907335081422450087952448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2897]
theorem treeEq2896 : B2896.tree = HexagonCover.NBand.M6667_6700.SplitData.node2896 := by
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
  · exact treeEq2897

def B2895 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820541041988555074170257472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2896, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq2895 : B2895.tree = HexagonCover.NBand.M6667_6700.SplitData.node2895 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2896
  · rfl
  · rfl

def B2548 : Block := .branch 101 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![Tip2544_2549, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B2895]
theorem treeEq2548 : B2548.tree = HexagonCover.NBand.M6667_6700.SplitData.node2548 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2895

def B2900 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180749340131798850933144245764160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq2900 : B2900.tree = HexagonCover.NBand.M6667_6700.SplitData.node2900 := by
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

def B2899 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060462705781061944869306783760448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2900]
theorem treeEq2899 : B2899.tree = HexagonCover.NBand.M6667_6700.SplitData.node2899 := by
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
  · exact treeEq2900

def B2898 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358536920414768852001930866065472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2899, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 958).pointIds 958)]
theorem treeEq2898 : B2898.tree = HexagonCover.NBand.M6667_6700.SplitData.node2898 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2899
  · rfl
  · rfl

def B2547 : Block := .branch 91 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![B2548, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B2898]
theorem treeEq2547 : B2547.tree = HexagonCover.NBand.M6667_6700.SplitData.node2547 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2548
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2898

def B2903 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040558027635171373431593107520] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq2903 : B2903.tree = HexagonCover.NBand.M6667_6700.SplitData.node2903 := by
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

def B2902 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923676898265309594131103808] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2903]
theorem treeEq2902 : B2902.tree = HexagonCover.NBand.M6667_6700.SplitData.node2902 := by
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
  · exact treeEq2903

def B2901 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138310605172442218213408832] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2902, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq2901 : B2901.tree = HexagonCover.NBand.M6667_6700.SplitData.node2901 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2902
  · rfl
  · rfl

def B2546 : Block := .branch 89 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 117).pointIds 117), B2547, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B2901]
theorem treeEq2546 : B2546.tree = HexagonCover.NBand.M6667_6700.SplitData.node2546 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2547
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2901

def B2906 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929078925041369935500542016] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq2906 : B2906.tree = HexagonCover.NBand.M6667_6700.SplitData.node2906 := by
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

def B2905 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294728188135306098038538304] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2906]
theorem treeEq2905 : B2905.tree = HexagonCover.NBand.M6667_6700.SplitData.node2905 := by
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
  · exact treeEq2906

def B2904 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461422011952099789096296644672] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2905, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq2904 : B2904.tree = HexagonCover.NBand.M6667_6700.SplitData.node2904 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2905
  · rfl
  · rfl

def B2545 : Block := .branch 86 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B2546, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B2904]
theorem treeEq2545 : B2545.tree = HexagonCover.NBand.M6667_6700.SplitData.node2545 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2546
  · rfl
  · rfl
  · exact treeEq2904

def B2909 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6734599544820800647083213573217930360669883178942528] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 965).pointIds 965)]
theorem treeEq2909 : B2909.tree = HexagonCover.NBand.M6667_6700.SplitData.node2909 := by
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

def B2908 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 5986310706507378352962926938867193454606045716938816] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2909]
theorem treeEq2908 : B2908.tree = HexagonCover.NBand.M6667_6700.SplitData.node2908 := by
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
  · exact treeEq2909

def B2907 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 5986310706507378354261001153500900361738669799243840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2908, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq2907 : B2907.tree = HexagonCover.NBand.M6667_6700.SplitData.node2907 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2908
  · rfl
  · rfl

def B2544 : Block := .branch 85 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B2545, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B2907]
theorem treeEq2544 : B2544.tree = HexagonCover.NBand.M6667_6700.SplitData.node2544 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2545
  · rfl
  · rfl
  · exact treeEq2907

theorem accepted2544 : B2544.accepted = true := by decide +kernel
theorem checked2544 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2544 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq2544]
  exact B2544.sound accepted2544
#print axioms checked2544

def B2921 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864553951735076251741192256] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq2921 : B2921.tree = HexagonCover.NBand.M6667_6700.SplitData.node2921 := by
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

def B2920 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230203214829012414279188544] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2921]
theorem treeEq2920 : B2920.tree = HexagonCover.NBand.M6667_6700.SplitData.node2920 := by
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
  · exact treeEq2921

def B2919 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444836921736145038361493568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2920, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq2919 : B2919.tree = HexagonCover.NBand.M6667_6700.SplitData.node2919 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2920
  · rfl
  · rfl

def B2924 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 1298074234354309339596812249989184] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq2924 : B2924.tree = HexagonCover.NBand.M6667_6700.SplitData.node2924 := by
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

def B2923 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2924, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq2923 : B2923.tree = HexagonCover.NBand.M6667_6700.SplitData.node2923 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2924
  · rfl
  · rfl

def B2922 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2923, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq2922 : B2922.tree = HexagonCover.NBand.M6667_6700.SplitData.node2922 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2923
  · rfl

def B2918 : Block := .branch 84 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B2919, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B2922]
theorem treeEq2918 : B2918.tree = HexagonCover.NBand.M6667_6700.SplitData.node2918 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2919
  · rfl
  · rfl
  · exact treeEq2922

def B2927 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq2927 : B2927.tree = HexagonCover.NBand.M6667_6700.SplitData.node2927 := by
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

def B2926 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2927, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq2926 : B2926.tree = HexagonCover.NBand.M6667_6700.SplitData.node2926 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2927
  · rfl
  · rfl

def B2925 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2926, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq2925 : B2925.tree = HexagonCover.NBand.M6667_6700.SplitData.node2925 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2926
  · rfl

def B2917 : Block := .branch 80 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![B2918, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B2925]
theorem treeEq2917 : B2917.tree = HexagonCover.NBand.M6667_6700.SplitData.node2917 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2918
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2925

def B2916 : Block := .branch 95 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), B2917, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq2916 : B2916.tree = HexagonCover.NBand.M6667_6700.SplitData.node2916 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2917
  · rfl
  · rfl
  · rfl

theorem accepted2916 : B2916.accepted = true := by decide +kernel
theorem checked2916 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2916 (maskNeeds ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952]) := by
  rw [← treeEq2916]
  exact B2916.sound accepted2916
#print axioms checked2916

end HexagonCover.NBand.M6667_6700.SplitTree.Run0039
