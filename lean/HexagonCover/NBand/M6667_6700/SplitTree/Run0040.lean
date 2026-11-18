import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0030
import HexagonCover.NBand.M6667_6700.SplitTree.Run0031
import HexagonCover.NBand.M6667_6700.SplitTree.Run0034
import HexagonCover.NBand.M6667_6700.SplitTree.Run0039
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0040
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2274_2276 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2276 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0034.checked2276
def B2526 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1049).pointIds 1049)]
theorem treeEq2526 : B2526.tree = HexagonCover.NBand.M6667_6700.SplitData.node2526 := by
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

def B2525 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156713806814526015499804044744216479793216] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2526, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1048).pointIds 1048)]
theorem treeEq2525 : B2525.tree = HexagonCover.NBand.M6667_6700.SplitData.node2525 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2526
  · rfl
  · rfl

def B2524 : Block := .branch 121 ![385, 1297037792194332162, 9007199254747140, 24584, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 460).pointIds 460), (.leaf 5 (Common.fact 430).pointIds 430), B2525]
theorem treeEq2524 : B2524.tree = HexagonCover.NBand.M6667_6700.SplitData.node2524 := by
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
  · exact treeEq2525

def B2523 : Block := .branch 149 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B2524, (.leaf 5 (Common.fact 1046).pointIds 1046), (.leaf 6 (Common.fact 1047).pointIds 1047)]
theorem treeEq2523 : B2523.tree = HexagonCover.NBand.M6667_6700.SplitData.node2523 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2524
  · rfl
  · rfl

def B2522 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2523, (.leaf 6 (Common.fact 1045).pointIds 1045)]
theorem treeEq2522 : B2522.tree = HexagonCover.NBand.M6667_6700.SplitData.node2522 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2523
  · rfl

def B2275 : Block := .branch 80 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![Tip2274_2276, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B2522]
theorem treeEq2275 : B2275.tree = HexagonCover.NBand.M6667_6700.SplitData.node2275 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2522

def B2532 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864478393871350337417773120] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 871).pointIds 871)]
theorem treeEq2532 : B2532.tree = HexagonCover.NBand.M6667_6700.SplitData.node2532 := by
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

def B2531 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230127656965286499955769408] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2532]
theorem treeEq2531 : B2531.tree = HexagonCover.NBand.M6667_6700.SplitData.node2531 := by
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
  · exact treeEq2532

def B2530 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2531, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq2530 : B2530.tree = HexagonCover.NBand.M6667_6700.SplitData.node2530 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2531
  · rfl
  · rfl

def B2535 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 880).pointIds 880)]
theorem treeEq2535 : B2535.tree = HexagonCover.NBand.M6667_6700.SplitData.node2535 := by
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

def B2534 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2535, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 879).pointIds 879)]
theorem treeEq2534 : B2534.tree = HexagonCover.NBand.M6667_6700.SplitData.node2534 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2535
  · rfl
  · rfl

def B2533 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2534, (.leaf 6 (Common.fact 876).pointIds 876)]
theorem treeEq2533 : B2533.tree = HexagonCover.NBand.M6667_6700.SplitData.node2533 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2534
  · rfl

def B2529 : Block := .branch 84 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B2530, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B2533]
theorem treeEq2529 : B2529.tree = HexagonCover.NBand.M6667_6700.SplitData.node2529 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2530
  · rfl
  · rfl
  · exact treeEq2533

def B2538 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 883).pointIds 883)]
theorem treeEq2538 : B2538.tree = HexagonCover.NBand.M6667_6700.SplitData.node2538 := by
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

def B2537 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2538, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq2537 : B2537.tree = HexagonCover.NBand.M6667_6700.SplitData.node2537 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2538
  · rfl
  · rfl

def B2536 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2537, (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq2536 : B2536.tree = HexagonCover.NBand.M6667_6700.SplitData.node2536 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2537
  · rfl

def B2528 : Block := .branch 80 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![B2529, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B2536]
theorem treeEq2528 : B2528.tree = HexagonCover.NBand.M6667_6700.SplitData.node2528 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2529
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2536

def B2527 : Block := .branch 95 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), B2528, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 1050).pointIds 1050)]
theorem treeEq2527 : B2527.tree = HexagonCover.NBand.M6667_6700.SplitData.node2527 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2528
  · rfl
  · rfl
  · rfl

def B2274 : Block := .branch 78 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 87).pointIds 87), B2275, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B2527]
theorem treeEq2274 : B2274.tree = HexagonCover.NBand.M6667_6700.SplitData.node2274 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2275
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2527

theorem accepted2274 : B2274.accepted = true := by decide +kernel
theorem checked2274 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2274 (maskNeeds ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2274]
  exact B2274.sound accepted2274
#print axioms checked2274

def Tip1734_1889 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1889 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] HexagonCover.NBand.M6667_6700.SplitTree.Run0030.checked1889
def Tip1734_2261 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2261 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] HexagonCover.NBand.M6667_6700.SplitTree.Run0031.checked2261
def Tip1734_1735 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1735 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0031.checked1735
def B1888 : Block := .branch 137 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), Tip1734_1889, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq1888 : B1888.tree = HexagonCover.NBand.M6667_6700.SplitData.node1888 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1887 : Block := .branch 138 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B1888, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq1887 : B1887.tree = HexagonCover.NBand.M6667_6700.SplitData.node1887 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1888
  · rfl
  · rfl

def B2257 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261001134158087247904603003945024] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq2257 : B2257.tree = HexagonCover.NBand.M6667_6700.SplitData.node2257 := by
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

def B2256 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2257, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq2256 : B2256.tree = HexagonCover.NBand.M6667_6700.SplitData.node2256 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2257
  · rfl
  · rfl

def B2255 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2256, (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq2255 : B2255.tree = HexagonCover.NBand.M6667_6700.SplitData.node2255 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2256
  · rfl

def B1886 : Block := .branch 84 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B1887, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B2255]
theorem treeEq1886 : B1886.tree = HexagonCover.NBand.M6667_6700.SplitData.node1886 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1887
  · rfl
  · rfl
  · exact treeEq2255

def B2260 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq2260 : B2260.tree = HexagonCover.NBand.M6667_6700.SplitData.node2260 := by
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

def B2259 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2260, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq2259 : B2259.tree = HexagonCover.NBand.M6667_6700.SplitData.node2259 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2260
  · rfl
  · rfl

def B2258 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2259, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq2258 : B2258.tree = HexagonCover.NBand.M6667_6700.SplitData.node2258 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2259
  · rfl

def B1885 : Block := .branch 80 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![B1886, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B2258]
theorem treeEq1885 : B1885.tree = HexagonCover.NBand.M6667_6700.SplitData.node1885 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1886
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2258

def B1884 : Block := .branch 78 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 87).pointIds 87), B1885, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip1734_2261]
theorem treeEq1884 : B1884.tree = HexagonCover.NBand.M6667_6700.SplitData.node1884 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1885
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1734 : Block := .branch 76 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), Tip1734_1735, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), B1884]
theorem treeEq1734 : B1734.tree = HexagonCover.NBand.M6667_6700.SplitData.node1734 := by
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
  · exact treeEq1884

theorem accepted1734 : B1734.accepted = true := by decide +kernel
theorem checked1734 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1734 (maskNeeds ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq1734]
  exact B1734.sound accepted1734
#print axioms checked1734

def Tip1733_2544 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2544 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] HexagonCover.NBand.M6667_6700.SplitTree.Run0039.checked2544
def Tip1733_2916 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2916 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] HexagonCover.NBand.M6667_6700.SplitTree.Run0039.checked2916
def Tip1733_2274 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2274 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] checked2274
def Tip1733_1734 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1734 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] checked1734
def B2543 : Block := .branch 137 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 997).pointIds 997), Tip1733_2544, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq2543 : B2543.tree = HexagonCover.NBand.M6667_6700.SplitData.node2543 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2542 : Block := .branch 138 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 995).pointIds 995), B2543, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq2542 : B2542.tree = HexagonCover.NBand.M6667_6700.SplitData.node2542 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2543
  · rfl
  · rfl

def B2912 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261001134158087247904603003945024] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq2912 : B2912.tree = HexagonCover.NBand.M6667_6700.SplitData.node2912 := by
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

def B2911 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2912, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq2911 : B2911.tree = HexagonCover.NBand.M6667_6700.SplitData.node2911 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2912
  · rfl
  · rfl

def B2910 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2911, (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq2910 : B2910.tree = HexagonCover.NBand.M6667_6700.SplitData.node2910 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2911
  · rfl

def B2541 : Block := .branch 84 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B2542, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B2910]
theorem treeEq2541 : B2541.tree = HexagonCover.NBand.M6667_6700.SplitData.node2541 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2542
  · rfl
  · rfl
  · exact treeEq2910

def B2915 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq2915 : B2915.tree = HexagonCover.NBand.M6667_6700.SplitData.node2915 := by
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

def B2914 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2915, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq2914 : B2914.tree = HexagonCover.NBand.M6667_6700.SplitData.node2914 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2915
  · rfl
  · rfl

def B2913 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2914, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq2913 : B2913.tree = HexagonCover.NBand.M6667_6700.SplitData.node2913 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2914
  · rfl

def B2540 : Block := .branch 80 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![B2541, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B2913]
theorem treeEq2540 : B2540.tree = HexagonCover.NBand.M6667_6700.SplitData.node2540 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2541
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2913

def B2539 : Block := .branch 78 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 87).pointIds 87), B2540, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip1733_2916]
theorem treeEq2539 : B2539.tree = HexagonCover.NBand.M6667_6700.SplitData.node2539 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2540
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2273 : Block := .branch 76 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), Tip1733_2274, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), B2539]
theorem treeEq2273 : B2273.tree = HexagonCover.NBand.M6667_6700.SplitData.node2273 := by
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
  · exact treeEq2539

def B1733 : Block := .branch 71 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 78).pointIds 78), (.leaf 1 (Common.fact 79).pointIds 79), Tip1733_1734, B2273, (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), (.leaf 0 [] 0)]
theorem treeEq1733 : B1733.tree = HexagonCover.NBand.M6667_6700.SplitData.node1733 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2273
  · rfl
  · rfl
  · rfl

theorem accepted1733 : B1733.accepted = true := by decide +kernel
theorem checked1733 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1733 (maskNeeds ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq1733]
  exact B1733.sound accepted1733
#print axioms checked1733

def Tip1729_1733 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1733 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] checked1733
def B2935 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394477139642005823272909141255386130645008, 393248, 1870722095783555735301033498527046896463107262513216] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 1212).pointIds 1212), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1213).pointIds 1213)]
theorem treeEq2935 : B2935.tree = HexagonCover.NBand.M6667_6700.SplitData.node2935 := by
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

def B2934 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 1394477139642005823272909141255386130645008, 187072209578355573530071658587684226515959365894176, 374144419156711147060460229825573084335432338505792] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 738).pointIds 738), B2935]
theorem treeEq2934 : B2934.tree = HexagonCover.NBand.M6667_6700.SplitData.node2934 := by
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
  · exact treeEq2935

def B2933 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 1394477139642005823272909141255386130645008, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 1210).pointIds 1210), B2934, (.leaf 6 (Common.fact 1211).pointIds 1211)]
theorem treeEq2933 : B2933.tree = HexagonCover.NBand.M6667_6700.SplitData.node2933 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2934
  · rfl

def B2932 : Block := .branch 129 ![385, 1297037792194332162, 9007199254747140, 24584, 1393796574908163946345982392040522594222096, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B2933, (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 1209).pointIds 1209)]
theorem treeEq2932 : B2932.tree = HexagonCover.NBand.M6667_6700.SplitData.node2932 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2933
  · rfl
  · rfl

def B2931 : Block := .branch 139 ![385, 1297037792194332162, 9007199254747140, 24584, 1393796574908163946345982392040522594222096, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B2932, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1208).pointIds 1208)]
theorem treeEq2931 : B2931.tree = HexagonCover.NBand.M6667_6700.SplitData.node2931 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2932
  · rfl
  · rfl

def B2930 : Block := .branch 106 ![385, 1297037792194332162, 9007199254747140, 24584, 1393796574908163946345982392040522594222096, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 1058).pointIds 1058), (.leaf 1 (Common.fact 1059).pointIds 1059), (.leaf 2 (Common.fact 1060).pointIds 1060), B2931, (.leaf 4 (Common.fact 1061).pointIds 1061), (.leaf 5 (Common.fact 1062).pointIds 1062), (.leaf 6 (Common.fact 1207).pointIds 1207)]
theorem treeEq2930 : B2930.tree = HexagonCover.NBand.M6667_6700.SplitData.node2930 := by
  change Tree.branch (106 : Fin 173) _ = Tree.branch (106 : Fin 173) _
  apply congrArg (Tree.branch (106 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2931
  · rfl
  · rfl
  · rfl

def B2929 : Block := .branch 117 ![385, 1297037792194332162, 9007199254747140, 24584, 1393796574908163946345982392040522594222096, 393248, 6360455125664089501321461344565289354679504468443200] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 778).pointIds 778), (.leaf 2 (Common.fact 779).pointIds 779), B2930, (.leaf 4 (Common.fact 1056).pointIds 1056), (.leaf 5 (Common.fact 781).pointIds 781), (.leaf 6 (Common.fact 1206).pointIds 1206)]
theorem treeEq2929 : B2929.tree = HexagonCover.NBand.M6667_6700.SplitData.node2929 := by
  change Tree.branch (117 : Fin 173) _ = Tree.branch (117 : Fin 173) _
  apply congrArg (Tree.branch (117 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2930
  · rfl
  · rfl
  · rfl

def B2928 : Block := .branch 140 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321461344565289354679504468443200] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2929, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1205).pointIds 1205)]
theorem treeEq2928 : B2928.tree = HexagonCover.NBand.M6667_6700.SplitData.node2928 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2929
  · rfl
  · rfl

def B1732 : Block := .branch 67 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 73).pointIds 73), Tip1729_1733, (.leaf 2 (Common.fact 74).pointIds 74), (.leaf 3 (Common.fact 75).pointIds 75), (.leaf 4 (Common.fact 76).pointIds 76), (.leaf 5 (Common.fact 77).pointIds 77), B2928]
theorem treeEq1732 : B1732.tree = HexagonCover.NBand.M6667_6700.SplitData.node1732 := by
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
  · exact treeEq2928

def B2938 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389810221183143480131648] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1216).pointIds 1216)]
theorem treeEq2938 : B2938.tree = HexagonCover.NBand.M6667_6700.SplitData.node2938 := by
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

def B2937 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389810221183143480131648] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2938, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1215).pointIds 1215)]
theorem treeEq2937 : B2937.tree = HexagonCover.NBand.M6667_6700.SplitData.node2937 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2938
  · rfl
  · rfl

def B2936 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 5986310706507378354261318027389810221183143480131648] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2937, (.leaf 6 (Common.fact 1214).pointIds 1214)]
theorem treeEq2936 : B2936.tree = HexagonCover.NBand.M6667_6700.SplitData.node2936 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2937
  · rfl

def B1731 : Block := .branch 65 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 68).pointIds 68), (.leaf 1 (Common.fact 69).pointIds 69), B1732, (.leaf 3 (Common.fact 70).pointIds 70), (.leaf 4 (Common.fact 71).pointIds 71), (.leaf 5 (Common.fact 72).pointIds 72), B2936]
theorem treeEq1731 : B1731.tree = HexagonCover.NBand.M6667_6700.SplitData.node1731 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1732
  · rfl
  · rfl
  · rfl
  · exact treeEq2936

def B1730 : Block := .branch 83 ![385, 1297037792194332162, 18455751272964298756, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 99).pointIds 99), B1731, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), (.leaf 6 (Common.fact 989).pointIds 989)]
theorem treeEq1730 : B1730.tree = HexagonCover.NBand.M6667_6700.SplitData.node1730 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1731
  · rfl
  · rfl
  · rfl

def B2941 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389791774439069770580032] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1219).pointIds 1219)]
theorem treeEq2941 : B2941.tree = HexagonCover.NBand.M6667_6700.SplitData.node2941 := by
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

def B2940 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389791774439069770580032] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2941, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1218).pointIds 1218)]
theorem treeEq2940 : B2940.tree = HexagonCover.NBand.M6667_6700.SplitData.node2940 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2941
  · rfl
  · rfl

def B2939 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 5986310706507378354261318027389791774439069770580032] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2940, (.leaf 6 (Common.fact 1217).pointIds 1217)]
theorem treeEq2939 : B2939.tree = HexagonCover.NBand.M6667_6700.SplitData.node2939 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2940
  · rfl

def B1729 : Block := .branch 64 ![385, 1297037792194332162, 9007199254747140, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 63).pointIds 63), (.leaf 1 (Common.fact 64).pointIds 64), B1730, (.leaf 3 (Common.fact 65).pointIds 65), (.leaf 4 (Common.fact 66).pointIds 66), (.leaf 5 (Common.fact 67).pointIds 67), B2939]
theorem treeEq1729 : B1729.tree = HexagonCover.NBand.M6667_6700.SplitData.node1729 := by
  change Tree.branch (64 : Fin 173) _ = Tree.branch (64 : Fin 173) _
  apply congrArg (Tree.branch (64 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1730
  · rfl
  · rfl
  · rfl
  · exact treeEq2939

theorem accepted1729 : B1729.accepted = true := by decide +kernel
theorem checked1729 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1729 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq1729]
  exact B1729.sound accepted1729
#print axioms checked1729

end HexagonCover.NBand.M6667_6700.SplitTree.Run0040
