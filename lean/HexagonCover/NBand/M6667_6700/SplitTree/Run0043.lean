import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0042
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0043
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3002_3008 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3008 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898223568507510070812606528] HexagonCover.NBand.M6667_6700.SplitTree.Run0042.checked3008
def B3005 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1010).pointIds 1010)]
theorem treeEq3005 : B3005.tree = HexagonCover.NBand.M6667_6700.SplitData.node3005 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3004 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3005, (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq3004 : B3004.tree = HexagonCover.NBand.M6667_6700.SplitData.node3004 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3005
  · rfl

def B3003 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387129931434873594290709725248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B3004]
theorem treeEq3003 : B3003.tree = HexagonCover.NBand.M6667_6700.SplitData.node3003 := by
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
  · exact treeEq3004

def B3099 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq3099 : B3099.tree = HexagonCover.NBand.M6667_6700.SplitData.node3099 := by
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

def B3098 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B3099]
theorem treeEq3098 : B3098.tree = HexagonCover.NBand.M6667_6700.SplitData.node3098 := by
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
  · exact treeEq3099

def B3102 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq3102 : B3102.tree = HexagonCover.NBand.M6667_6700.SplitData.node3102 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3101 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3102]
theorem treeEq3101 : B3101.tree = HexagonCover.NBand.M6667_6700.SplitData.node3101 := by
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
  · exact treeEq3102

def B3100 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3101, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq3100 : B3100.tree = HexagonCover.NBand.M6667_6700.SplitData.node3100 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3101
  · rfl
  · rfl

def B3097 : Block := .branch 119 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B3098, (.leaf 5 (Common.fact 419).pointIds 419), B3100]
theorem treeEq3097 : B3097.tree = HexagonCover.NBand.M6667_6700.SplitData.node3097 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3098
  · rfl
  · exact treeEq3100

def B3104 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq3104 : B3104.tree = HexagonCover.NBand.M6667_6700.SplitData.node3104 := by
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

def B3103 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3104, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq3103 : B3103.tree = HexagonCover.NBand.M6667_6700.SplitData.node3103 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3104
  · rfl
  · rfl

def B3096 : Block := .branch 112 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B3097, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B3103]
theorem treeEq3096 : B3096.tree = HexagonCover.NBand.M6667_6700.SplitData.node3096 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3097
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3103

def B3007 : Block := .branch 111 ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] ![Tip3002_3008, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B3096]
theorem treeEq3007 : B3007.tree = HexagonCover.NBand.M6667_6700.SplitData.node3007 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3096

def B3108 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892964684172901004342090038286745664] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1271).pointIds 1271)]
theorem treeEq3108 : B3108.tree = HexagonCover.NBand.M6667_6700.SplitData.node3108 := by
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

def B3107 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598844397538550267436026200824741952] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3108]
theorem treeEq3107 : B3107.tree = HexagonCover.NBand.M6667_6700.SplitData.node3107 := by
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
  · exact treeEq3108

def B3106 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374875169975376600142471753183974343158824907046976] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3107, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1270).pointIds 1270)]
theorem treeEq3106 : B3106.tree = HexagonCover.NBand.M6667_6700.SplitData.node3106 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3107
  · rfl
  · rfl

def B3105 : Block := .branch 159 ![385, 618970609938500496155215362, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374144419156711148683369910767616201648996940775488] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 1269).pointIds 1269), (.leaf 2 (Common.fact 1250).pointIds 1250), (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), B3106]
theorem treeEq3105 : B3105.tree = HexagonCover.NBand.M6667_6700.SplitData.node3105 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3106

def B3006 : Block := .branch 69 ![1152921504606847361, 618970019642690137449563650, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] ![B3007, B3105, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1011).pointIds 1011)]
theorem treeEq3006 : B3006.tree = HexagonCover.NBand.M6667_6700.SplitData.node3006 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3007
  · exact treeEq3105
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3002 : Block := .branch 108 ![1152921504606847361, 618970019642690137449563650, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B3003, (.leaf 5 (Common.fact 136).pointIds 136), B3006]
theorem treeEq3002 : B3002.tree = HexagonCover.NBand.M6667_6700.SplitData.node3002 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3003
  · rfl
  · exact treeEq3006

theorem accepted3002 : B3002.accepted = true := by decide +kernel
theorem checked3002 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3002 (maskNeeds ![1152921504606847361, 618970019642690137449563650, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272]) := by
  rw [← treeEq3002]
  exact B3002.sound accepted3002
#print axioms checked3002

def Tip2998_3002 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3002 ![1152921504606847361, 618970019642690137449563650, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] checked3002
def B3112 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1033).pointIds 1033)]
theorem treeEq3112 : B3112.tree = HexagonCover.NBand.M6667_6700.SplitData.node3112 := by
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

def B3111 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3112, (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq3111 : B3111.tree = HexagonCover.NBand.M6667_6700.SplitData.node3111 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3112
  · rfl

def B3110 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605831777217696535764533312] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3111]
theorem treeEq3110 : B3110.tree = HexagonCover.NBand.M6667_6700.SplitData.node3110 := by
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
  · exact treeEq3111

def B3109 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820465484124829159846838336] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3110, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq3109 : B3109.tree = HexagonCover.NBand.M6667_6700.SplitData.node3109 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3110
  · rfl
  · rfl

def B3001 : Block := .branch 101 ![1152921504606847361, 618970019642690137449563650, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![Tip2998_3002, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B3109]
theorem treeEq3001 : B3001.tree = HexagonCover.NBand.M6667_6700.SplitData.node3001 := by
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
  · exact treeEq3109

def B3116 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 187072209578355573530071658587684226515959365894176, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 1036).pointIds 1036)]
theorem treeEq3116 : B3116.tree = HexagonCover.NBand.M6667_6700.SplitData.node3116 := by
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
  · rfl

def B3115 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511795441116629495843142850553700679744] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), B3116, (.leaf 6 (Common.fact 1035).pointIds 1035)]
theorem treeEq3115 : B3115.tree = HexagonCover.NBand.M6667_6700.SplitData.node3115 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3116
  · rfl

def B3114 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3115]
theorem treeEq3114 : B3114.tree = HexagonCover.NBand.M6667_6700.SplitData.node3114 := by
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
  · exact treeEq3115

def B3113 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3114, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1034).pointIds 1034)]
theorem treeEq3113 : B3113.tree = HexagonCover.NBand.M6667_6700.SplitData.node3113 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3114
  · rfl
  · rfl

def B3000 : Block := .branch 91 ![1152921504606847361, 618970019642690137449563650, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![B3001, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B3113]
theorem treeEq3000 : B3000.tree = HexagonCover.NBand.M6667_6700.SplitData.node3000 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3001
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3113

def B3120 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1039).pointIds 1039)]
theorem treeEq3120 : B3120.tree = HexagonCover.NBand.M6667_6700.SplitData.node3120 := by
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

def B3119 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3120, (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq3119 : B3119.tree = HexagonCover.NBand.M6667_6700.SplitData.node3119 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3120
  · rfl

def B3118 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923601340401583679807684672] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3119]
theorem treeEq3118 : B3118.tree = HexagonCover.NBand.M6667_6700.SplitData.node3118 := by
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
  · exact treeEq3119

def B3117 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138235047308716303889989696] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3118, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1037).pointIds 1037)]
theorem treeEq3117 : B3117.tree = HexagonCover.NBand.M6667_6700.SplitData.node3117 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3118
  · rfl
  · rfl

def B2999 : Block := .branch 89 ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 117).pointIds 117), B3000, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B3117]
theorem treeEq2999 : B2999.tree = HexagonCover.NBand.M6667_6700.SplitData.node2999 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3000
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3117

def B3124 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq3124 : B3124.tree = HexagonCover.NBand.M6667_6700.SplitData.node3124 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3123 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3124, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq3123 : B3123.tree = HexagonCover.NBand.M6667_6700.SplitData.node3123 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3124
  · rfl

def B3122 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294652630271580183715119168] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3123]
theorem treeEq3122 : B3122.tree = HexagonCover.NBand.M6667_6700.SplitData.node3122 := by
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
  · exact treeEq3123

def B3121 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461421936394236063181973225536] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3122, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq3121 : B3121.tree = HexagonCover.NBand.M6667_6700.SplitData.node3121 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3122
  · rfl
  · rfl

def B2998 : Block := .branch 86 ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B2999, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B3121]
theorem treeEq2998 : B2998.tree = HexagonCover.NBand.M6667_6700.SplitData.node2998 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2999
  · rfl
  · rfl
  · exact treeEq3121

theorem accepted2998 : B2998.accepted = true := by decide +kernel
theorem checked2998 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2998 (maskNeeds ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272]) := by
  rw [← treeEq2998]
  exact B2998.sound accepted2998
#print axioms checked2998

def Tip2993_2998 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2998 ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] checked2998
def B3127 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356890317740949975887586525248] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1041).pointIds 1041)]
theorem treeEq3127 : B3127.tree = HexagonCover.NBand.M6667_6700.SplitData.node3127 := by
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

def B3126 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070255967004043912050124521536] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3127]
theorem treeEq3126 : B3126.tree = HexagonCover.NBand.M6667_6700.SplitData.node3126 := by
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
  · exact treeEq3127

def B3125 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321144470600710951044674206826560] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3126, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq3125 : B3125.tree = HexagonCover.NBand.M6667_6700.SplitData.node3125 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3126
  · rfl
  · rfl

def B2997 : Block := .branch 85 ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), Tip2993_2998, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B3125]
theorem treeEq2997 : B2997.tree = HexagonCover.NBand.M6667_6700.SplitData.node2997 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3125

def B2996 : Block := .branch 137 ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B2997, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq2996 : B2996.tree = HexagonCover.NBand.M6667_6700.SplitData.node2996 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2997
  · rfl
  · rfl

def B2995 : Block := .branch 138 ![1152921504606847361, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B2996, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq2995 : B2995.tree = HexagonCover.NBand.M6667_6700.SplitData.node2995 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2996
  · rfl
  · rfl

def B3130 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1044).pointIds 1044)]
theorem treeEq3130 : B3130.tree = HexagonCover.NBand.M6667_6700.SplitData.node3130 := by
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

def B3129 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3130, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1043).pointIds 1043)]
theorem treeEq3129 : B3129.tree = HexagonCover.NBand.M6667_6700.SplitData.node3129 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3130
  · rfl
  · rfl

def B3128 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3129, (.leaf 6 (Common.fact 1042).pointIds 1042)]
theorem treeEq3128 : B3128.tree = HexagonCover.NBand.M6667_6700.SplitData.node3128 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3129
  · rfl

def B2994 : Block := .branch 84 ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B2995, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3128]
theorem treeEq2994 : B2994.tree = HexagonCover.NBand.M6667_6700.SplitData.node2994 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2995
  · rfl
  · rfl
  · exact treeEq3128

def B3135 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1049).pointIds 1049)]
theorem treeEq3135 : B3135.tree = HexagonCover.NBand.M6667_6700.SplitData.node3135 := by
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

def B3134 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156713806814526015499804044744216479793216] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3135, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1048).pointIds 1048)]
theorem treeEq3134 : B3134.tree = HexagonCover.NBand.M6667_6700.SplitData.node3134 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3135
  · rfl
  · rfl

def B3133 : Block := .branch 121 ![385, 1538, 1099511633924, 24584, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 460).pointIds 460), (.leaf 5 (Common.fact 430).pointIds 430), B3134]
theorem treeEq3133 : B3133.tree = HexagonCover.NBand.M6667_6700.SplitData.node3133 := by
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
  · exact treeEq3134

def B3132 : Block := .branch 149 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B3133, (.leaf 5 (Common.fact 1046).pointIds 1046), (.leaf 6 (Common.fact 1047).pointIds 1047)]
theorem treeEq3132 : B3132.tree = HexagonCover.NBand.M6667_6700.SplitData.node3132 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3133
  · rfl
  · rfl

def B3131 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3132, (.leaf 6 (Common.fact 1045).pointIds 1045)]
theorem treeEq3131 : B3131.tree = HexagonCover.NBand.M6667_6700.SplitData.node3131 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3132
  · rfl

def B2993 : Block := .branch 80 ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![B2994, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3131]
theorem treeEq2993 : B2993.tree = HexagonCover.NBand.M6667_6700.SplitData.node2993 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2994
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3131

theorem accepted2993 : B2993.accepted = true := by decide +kernel
theorem checked2993 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2993 (maskNeeds ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2993]
  exact B2993.sound accepted2993
#print axioms checked2993

def B3184 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3184 : B3184.tree = HexagonCover.NBand.M6667_6700.SplitData.node3184 := by
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

def B3183 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3184]
theorem treeEq3183 : B3183.tree = HexagonCover.NBand.M6667_6700.SplitData.node3183 := by
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
  · exact treeEq3184

def B3186 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq3186 : B3186.tree = HexagonCover.NBand.M6667_6700.SplitData.node3186 := by
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

def B3185 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3186, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3185 : B3185.tree = HexagonCover.NBand.M6667_6700.SplitData.node3185 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3186
  · rfl
  · rfl

def B3182 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3183, (.leaf 5 (Common.fact 439).pointIds 439), B3185]
theorem treeEq3182 : B3182.tree = HexagonCover.NBand.M6667_6700.SplitData.node3182 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3183
  · rfl
  · exact treeEq3185

def B3188 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3188 : B3188.tree = HexagonCover.NBand.M6667_6700.SplitData.node3188 := by
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

def B3187 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3188]
theorem treeEq3187 : B3187.tree = HexagonCover.NBand.M6667_6700.SplitData.node3187 := by
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
  · exact treeEq3188

def B3181 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3182, B3187, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3181 : B3181.tree = HexagonCover.NBand.M6667_6700.SplitData.node3181 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3182
  · exact treeEq3187
  · rfl
  · rfl

def B3191 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3191 : B3191.tree = HexagonCover.NBand.M6667_6700.SplitData.node3191 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3190 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3191]
theorem treeEq3190 : B3190.tree = HexagonCover.NBand.M6667_6700.SplitData.node3190 := by
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
  · exact treeEq3191

def B3189 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3190, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3189 : B3189.tree = HexagonCover.NBand.M6667_6700.SplitData.node3189 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3190
  · rfl
  · rfl

def B3180 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3181, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3189, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3180 : B3180.tree = HexagonCover.NBand.M6667_6700.SplitData.node3180 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3181
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3189
  · rfl

def B3194 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq3194 : B3194.tree = HexagonCover.NBand.M6667_6700.SplitData.node3194 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3193 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3194]
theorem treeEq3193 : B3193.tree = HexagonCover.NBand.M6667_6700.SplitData.node3193 := by
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
  · exact treeEq3194

def B3192 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3193, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq3192 : B3192.tree = HexagonCover.NBand.M6667_6700.SplitData.node3192 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3193
  · rfl
  · rfl

def B3179 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3180, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3192]
theorem treeEq3179 : B3179.tree = HexagonCover.NBand.M6667_6700.SplitData.node3179 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3180
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3192

def B3197 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1277).pointIds 1277)]
theorem treeEq3197 : B3197.tree = HexagonCover.NBand.M6667_6700.SplitData.node3197 := by
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

def B3196 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3197, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1276).pointIds 1276)]
theorem treeEq3196 : B3196.tree = HexagonCover.NBand.M6667_6700.SplitData.node3196 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3197
  · rfl
  · rfl

def B3195 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96732955035101812557373448, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841132979750612810287546432] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1275).pointIds 1275), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3196]
theorem treeEq3195 : B3195.tree = HexagonCover.NBand.M6667_6700.SplitData.node3195 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3196

def B3178 : Block := .branch 74 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B3179, B3195, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq3178 : B3178.tree = HexagonCover.NBand.M6667_6700.SplitData.node3178 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3179
  · exact treeEq3195
  · rfl
  · rfl
  · rfl

theorem accepted3178 : B3178.accepted = true := by decide +kernel
theorem checked3178 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3178 (maskNeeds ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656]) := by
  rw [← treeEq3178]
  exact B3178.sound accepted3178
#print axioms checked3178

end HexagonCover.NBand.M6667_6700.SplitTree.Run0043
