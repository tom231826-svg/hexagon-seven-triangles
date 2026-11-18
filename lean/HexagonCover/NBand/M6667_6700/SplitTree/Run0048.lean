import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0047
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0048
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3355_3362 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3362 ![1152921504606847361, 618970019642690137449563650, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] HexagonCover.NBand.M6667_6700.SplitTree.Run0047.checked3362
def B3361 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1010).pointIds 1010)]
theorem treeEq3361 : B3361.tree = HexagonCover.NBand.M6667_6700.SplitData.node3361 := by
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

def B3360 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3361, (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq3360 : B3360.tree = HexagonCover.NBand.M6667_6700.SplitData.node3360 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3361
  · rfl

def B3359 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387129931434873594290709725248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B3360]
theorem treeEq3359 : B3359.tree = HexagonCover.NBand.M6667_6700.SplitData.node3359 := by
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
  · exact treeEq3360

def B3358 : Block := .branch 108 ![1152921504606847361, 618970019642690137449563650, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B3359, (.leaf 5 (Common.fact 136).pointIds 136), Tip3355_3362]
theorem treeEq3358 : B3358.tree = HexagonCover.NBand.M6667_6700.SplitData.node3358 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3359
  · rfl
  · rfl

def B3483 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1033).pointIds 1033)]
theorem treeEq3483 : B3483.tree = HexagonCover.NBand.M6667_6700.SplitData.node3483 := by
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

def B3482 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3483, (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq3482 : B3482.tree = HexagonCover.NBand.M6667_6700.SplitData.node3482 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3483
  · rfl

def B3481 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605831777217696535764533312] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3482]
theorem treeEq3481 : B3481.tree = HexagonCover.NBand.M6667_6700.SplitData.node3481 := by
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
  · exact treeEq3482

def B3480 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820465484124829159846838336] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3481, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq3480 : B3480.tree = HexagonCover.NBand.M6667_6700.SplitData.node3480 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3481
  · rfl
  · rfl

def B3357 : Block := .branch 101 ![1152921504606847361, 618970019642690137449563650, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![B3358, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B3480]
theorem treeEq3357 : B3357.tree = HexagonCover.NBand.M6667_6700.SplitData.node3357 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3358
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3480

def B3487 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 187072209578355573530071658587684226515959365894176, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 1036).pointIds 1036)]
theorem treeEq3487 : B3487.tree = HexagonCover.NBand.M6667_6700.SplitData.node3487 := by
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

def B3486 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511795441116629495843142850553700679744] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), B3487, (.leaf 6 (Common.fact 1035).pointIds 1035)]
theorem treeEq3486 : B3486.tree = HexagonCover.NBand.M6667_6700.SplitData.node3486 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3487
  · rfl

def B3485 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3486]
theorem treeEq3485 : B3485.tree = HexagonCover.NBand.M6667_6700.SplitData.node3485 := by
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
  · exact treeEq3486

def B3484 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3485, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1034).pointIds 1034)]
theorem treeEq3484 : B3484.tree = HexagonCover.NBand.M6667_6700.SplitData.node3484 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3485
  · rfl
  · rfl

def B3356 : Block := .branch 91 ![1152921504606847361, 618970019642690137449563650, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![B3357, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B3484]
theorem treeEq3356 : B3356.tree = HexagonCover.NBand.M6667_6700.SplitData.node3356 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3357
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3484

def B3491 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1039).pointIds 1039)]
theorem treeEq3491 : B3491.tree = HexagonCover.NBand.M6667_6700.SplitData.node3491 := by
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

def B3490 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3491, (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq3490 : B3490.tree = HexagonCover.NBand.M6667_6700.SplitData.node3490 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3491
  · rfl

def B3489 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923601340401583679807684672] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3490]
theorem treeEq3489 : B3489.tree = HexagonCover.NBand.M6667_6700.SplitData.node3489 := by
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
  · exact treeEq3490

def B3488 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138235047308716303889989696] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3489, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1037).pointIds 1037)]
theorem treeEq3488 : B3488.tree = HexagonCover.NBand.M6667_6700.SplitData.node3488 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3489
  · rfl
  · rfl

def B3355 : Block := .branch 89 ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 117).pointIds 117), B3356, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B3488]
theorem treeEq3355 : B3355.tree = HexagonCover.NBand.M6667_6700.SplitData.node3355 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3356
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3488

theorem accepted3355 : B3355.accepted = true := by decide +kernel
theorem checked3355 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3355 (maskNeeds ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272]) := by
  rw [← treeEq3355]
  exact B3355.sound accepted3355
#print axioms checked3355

def Tip3350_3355 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3355 ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] checked3355
def B3495 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq3495 : B3495.tree = HexagonCover.NBand.M6667_6700.SplitData.node3495 := by
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

def B3494 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3495, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq3494 : B3494.tree = HexagonCover.NBand.M6667_6700.SplitData.node3494 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3495
  · rfl

def B3493 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294652630271580183715119168] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3494]
theorem treeEq3493 : B3493.tree = HexagonCover.NBand.M6667_6700.SplitData.node3493 := by
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
  · exact treeEq3494

def B3492 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461421936394236063181973225536] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3493, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq3492 : B3492.tree = HexagonCover.NBand.M6667_6700.SplitData.node3492 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3493
  · rfl
  · rfl

def B3354 : Block := .branch 86 ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), Tip3350_3355, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B3492]
theorem treeEq3354 : B3354.tree = HexagonCover.NBand.M6667_6700.SplitData.node3354 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3492

def B3498 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356890317740949975887586525248] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1041).pointIds 1041)]
theorem treeEq3498 : B3498.tree = HexagonCover.NBand.M6667_6700.SplitData.node3498 := by
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

def B3497 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070255967004043912050124521536] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3498]
theorem treeEq3497 : B3497.tree = HexagonCover.NBand.M6667_6700.SplitData.node3497 := by
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
  · exact treeEq3498

def B3496 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321144470600710951044674206826560] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3497, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq3496 : B3496.tree = HexagonCover.NBand.M6667_6700.SplitData.node3496 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3497
  · rfl
  · rfl

def B3353 : Block := .branch 85 ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B3354, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B3496]
theorem treeEq3353 : B3353.tree = HexagonCover.NBand.M6667_6700.SplitData.node3353 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3354
  · rfl
  · rfl
  · exact treeEq3496

def B3352 : Block := .branch 137 ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 997).pointIds 997), B3353, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq3352 : B3352.tree = HexagonCover.NBand.M6667_6700.SplitData.node3352 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3353
  · rfl
  · rfl

def B3351 : Block := .branch 138 ![1152921504606847361, 1538, 75557863727013835053060, 29016580853992535015579656, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 995).pointIds 995), B3352, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq3351 : B3351.tree = HexagonCover.NBand.M6667_6700.SplitData.node3351 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3352
  · rfl
  · rfl

def B3501 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1044).pointIds 1044)]
theorem treeEq3501 : B3501.tree = HexagonCover.NBand.M6667_6700.SplitData.node3501 := by
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

def B3500 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3501, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1043).pointIds 1043)]
theorem treeEq3500 : B3500.tree = HexagonCover.NBand.M6667_6700.SplitData.node3500 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3501
  · rfl
  · rfl

def B3499 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3500, (.leaf 6 (Common.fact 1042).pointIds 1042)]
theorem treeEq3499 : B3499.tree = HexagonCover.NBand.M6667_6700.SplitData.node3499 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3500
  · rfl

def B3350 : Block := .branch 84 ![1152921504606847361, 1538, 75576310471087544604676, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3351, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3499]
theorem treeEq3350 : B3350.tree = HexagonCover.NBand.M6667_6700.SplitData.node3350 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3351
  · rfl
  · rfl
  · exact treeEq3499

theorem accepted3350 : B3350.accepted = true := by decide +kernel
theorem checked3350 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3350 (maskNeeds ![1152921504606847361, 1538, 75576310471087544604676, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq3350]
  exact B3350.sound accepted3350
#print axioms checked3350

def B3561 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3561 : B3561.tree = HexagonCover.NBand.M6667_6700.SplitData.node3561 := by
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

def B3560 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3561]
theorem treeEq3560 : B3560.tree = HexagonCover.NBand.M6667_6700.SplitData.node3560 := by
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
  · exact treeEq3561

def B3563 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq3563 : B3563.tree = HexagonCover.NBand.M6667_6700.SplitData.node3563 := by
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

def B3562 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3563, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3562 : B3562.tree = HexagonCover.NBand.M6667_6700.SplitData.node3562 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3563
  · rfl
  · rfl

def B3559 : Block := .branch 128 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B3560, (.leaf 5 (Common.fact 439).pointIds 439), B3562]
theorem treeEq3559 : B3559.tree = HexagonCover.NBand.M6667_6700.SplitData.node3559 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3560
  · rfl
  · exact treeEq3562

def B3565 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3565 : B3565.tree = HexagonCover.NBand.M6667_6700.SplitData.node3565 := by
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

def B3564 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3565]
theorem treeEq3564 : B3564.tree = HexagonCover.NBand.M6667_6700.SplitData.node3564 := by
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
  · exact treeEq3565

def B3558 : Block := .branch 127 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3559, B3564, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3558 : B3558.tree = HexagonCover.NBand.M6667_6700.SplitData.node3558 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3559
  · exact treeEq3564
  · rfl
  · rfl

def B3568 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3568 : B3568.tree = HexagonCover.NBand.M6667_6700.SplitData.node3568 := by
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

def B3567 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3568]
theorem treeEq3567 : B3567.tree = HexagonCover.NBand.M6667_6700.SplitData.node3567 := by
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
  · exact treeEq3568

def B3566 : Block := .branch 167 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3567, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3566 : B3566.tree = HexagonCover.NBand.M6667_6700.SplitData.node3566 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3567
  · rfl
  · rfl

def B3557 : Block := .branch 125 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3558, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3566, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3557 : B3557.tree = HexagonCover.NBand.M6667_6700.SplitData.node3557 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3558
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3566
  · rfl

def B3571 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq3571 : B3571.tree = HexagonCover.NBand.M6667_6700.SplitData.node3571 := by
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

def B3570 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3571]
theorem treeEq3570 : B3570.tree = HexagonCover.NBand.M6667_6700.SplitData.node3570 := by
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
  · exact treeEq3571

def B3569 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3570, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq3569 : B3569.tree = HexagonCover.NBand.M6667_6700.SplitData.node3569 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3570
  · rfl
  · rfl

def B3556 : Block := .branch 123 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3557, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3569]
theorem treeEq3556 : B3556.tree = HexagonCover.NBand.M6667_6700.SplitData.node3556 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3557
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3569

theorem accepted3556 : B3556.accepted = true := by decide +kernel
theorem checked3556 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3556 (maskNeeds ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504]) := by
  rw [← treeEq3556]
  exact B3556.sound accepted3556
#print axioms checked3556

def Tip3555_3556 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3556 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] checked3556
def B3577 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3577 : B3577.tree = HexagonCover.NBand.M6667_6700.SplitData.node3577 := by
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

def B3576 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3577]
theorem treeEq3576 : B3576.tree = HexagonCover.NBand.M6667_6700.SplitData.node3576 := by
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
  · exact treeEq3577

def B3579 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq3579 : B3579.tree = HexagonCover.NBand.M6667_6700.SplitData.node3579 := by
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

def B3578 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3579, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3578 : B3578.tree = HexagonCover.NBand.M6667_6700.SplitData.node3578 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3579
  · rfl
  · rfl

def B3575 : Block := .branch 128 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B3576, (.leaf 5 (Common.fact 439).pointIds 439), B3578]
theorem treeEq3575 : B3575.tree = HexagonCover.NBand.M6667_6700.SplitData.node3575 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3576
  · rfl
  · exact treeEq3578

def B3581 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3581 : B3581.tree = HexagonCover.NBand.M6667_6700.SplitData.node3581 := by
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

def B3580 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3581]
theorem treeEq3580 : B3580.tree = HexagonCover.NBand.M6667_6700.SplitData.node3580 := by
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
  · exact treeEq3581

def B3574 : Block := .branch 127 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3575, B3580, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3574 : B3574.tree = HexagonCover.NBand.M6667_6700.SplitData.node3574 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3575
  · exact treeEq3580
  · rfl
  · rfl

def B3584 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3584 : B3584.tree = HexagonCover.NBand.M6667_6700.SplitData.node3584 := by
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

def B3583 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3584]
theorem treeEq3583 : B3583.tree = HexagonCover.NBand.M6667_6700.SplitData.node3583 := by
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
  · exact treeEq3584

def B3582 : Block := .branch 167 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3583, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3582 : B3582.tree = HexagonCover.NBand.M6667_6700.SplitData.node3582 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3583
  · rfl
  · rfl

def B3573 : Block := .branch 125 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3574, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3582, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3573 : B3573.tree = HexagonCover.NBand.M6667_6700.SplitData.node3573 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3574
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3582
  · rfl

def B3587 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq3587 : B3587.tree = HexagonCover.NBand.M6667_6700.SplitData.node3587 := by
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

def B3586 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3587]
theorem treeEq3586 : B3586.tree = HexagonCover.NBand.M6667_6700.SplitData.node3586 := by
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
  · exact treeEq3587

def B3585 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3586, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq3585 : B3585.tree = HexagonCover.NBand.M6667_6700.SplitData.node3585 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3586
  · rfl
  · rfl

def B3572 : Block := .branch 123 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3573, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3585]
theorem treeEq3572 : B3572.tree = HexagonCover.NBand.M6667_6700.SplitData.node3572 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3573
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3585

def B3555 : Block := .branch 74 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip3555_3556, B3572, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq3555 : B3555.tree = HexagonCover.NBand.M6667_6700.SplitData.node3555 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3572
  · rfl
  · rfl
  · rfl

theorem accepted3555 : B3555.accepted = true := by decide +kernel
theorem checked3555 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3555 (maskNeeds ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656]) := by
  rw [← treeEq3555]
  exact B3555.sound accepted3555
#print axioms checked3555

end HexagonCover.NBand.M6667_6700.SplitTree.Run0048
