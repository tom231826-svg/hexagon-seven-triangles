import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0044
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0045
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3238_3242 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3242 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] HexagonCover.NBand.M6667_6700.SplitTree.Run0044.checked3242
def Tip3238_3270 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3270 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] HexagonCover.NBand.M6667_6700.SplitTree.Run0044.checked3270
def B3264 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1277).pointIds 1277)]
theorem treeEq3264 : B3264.tree = HexagonCover.NBand.M6667_6700.SplitData.node3264 := by
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

def B3263 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3264, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1276).pointIds 1276)]
theorem treeEq3263 : B3263.tree = HexagonCover.NBand.M6667_6700.SplitData.node3263 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3264
  · rfl
  · rfl

def B3262 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96723510302136073266946056, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841132979750612810287546432] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1278).pointIds 1278), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3263]
theorem treeEq3262 : B3262.tree = HexagonCover.NBand.M6667_6700.SplitData.node3262 := by
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
  · exact treeEq3263

def B3241 : Block := .branch 73 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip3238_3242, B3262, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3241 : B3241.tree = HexagonCover.NBand.M6667_6700.SplitData.node3241 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3262
  · rfl
  · rfl
  · rfl

def B3267 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1277).pointIds 1277)]
theorem treeEq3267 : B3267.tree = HexagonCover.NBand.M6667_6700.SplitData.node3267 := by
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

def B3266 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3267, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1276).pointIds 1276)]
theorem treeEq3266 : B3266.tree = HexagonCover.NBand.M6667_6700.SplitData.node3266 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3267
  · rfl
  · rfl

def B3265 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96718787935653203621732360, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841132979750612810287546432] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1279).pointIds 1279), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3266]
theorem treeEq3265 : B3265.tree = HexagonCover.NBand.M6667_6700.SplitData.node3265 := by
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
  · exact treeEq3266

def B3240 : Block := .branch 72 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3241, B3265, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 915).pointIds 915)]
theorem treeEq3240 : B3240.tree = HexagonCover.NBand.M6667_6700.SplitData.node3240 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3241
  · exact treeEq3265
  · rfl
  · rfl
  · rfl

def B3239 : Block := .branch 163 ![5319508131568930906582414993892835713, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B3240]
theorem treeEq3239 : B3239.tree = HexagonCover.NBand.M6667_6700.SplitData.node3239 := by
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
  · exact treeEq3240

def B3292 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1281).pointIds 1281)]
theorem treeEq3292 : B3292.tree = HexagonCover.NBand.M6667_6700.SplitData.node3292 := by
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

def B3291 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3292, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1280).pointIds 1280)]
theorem treeEq3291 : B3291.tree = HexagonCover.NBand.M6667_6700.SplitData.node3291 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3292
  · rfl
  · rfl

def B3290 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96723510302136073266946056, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502134741101683803948580928] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1278).pointIds 1278), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3291]
theorem treeEq3290 : B3290.tree = HexagonCover.NBand.M6667_6700.SplitData.node3290 := by
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
  · exact treeEq3291

def B3269 : Block := .branch 73 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip3238_3270, B3290, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq3269 : B3269.tree = HexagonCover.NBand.M6667_6700.SplitData.node3269 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3290
  · rfl
  · rfl
  · rfl

def B3295 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1281).pointIds 1281)]
theorem treeEq3295 : B3295.tree = HexagonCover.NBand.M6667_6700.SplitData.node3295 := by
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

def B3294 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3295, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1280).pointIds 1280)]
theorem treeEq3294 : B3294.tree = HexagonCover.NBand.M6667_6700.SplitData.node3294 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3295
  · rfl
  · rfl

def B3293 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96718787935653203621732360, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502134741101683803948580928] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1279).pointIds 1279), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3294]
theorem treeEq3293 : B3293.tree = HexagonCover.NBand.M6667_6700.SplitData.node3293 := by
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
  · exact treeEq3294

def B3268 : Block := .branch 72 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3269, B3293, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq3268 : B3268.tree = HexagonCover.NBand.M6667_6700.SplitData.node3268 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3269
  · exact treeEq3293
  · rfl
  · rfl
  · rfl

def B3238 : Block := .branch 122 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] ![B3239, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B3268]
theorem treeEq3238 : B3238.tree = HexagonCover.NBand.M6667_6700.SplitData.node3238 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3239
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3268

theorem accepted3238 : B3238.accepted = true := by decide +kernel
theorem checked3238 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3238 (maskNeeds ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848]) := by
  rw [← treeEq3238]
  exact B3238.sound accepted3238
#print axioms checked3238

def Tip3163_3174 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3174 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] HexagonCover.NBand.M6667_6700.SplitTree.Run0044.checked3174
def Tip3163_3238 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3238 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] checked3238
def B3165 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq3165 : B3165.tree = HexagonCover.NBand.M6667_6700.SplitData.node3165 := by
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

def B3164 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B3165]
theorem treeEq3164 : B3164.tree = HexagonCover.NBand.M6667_6700.SplitData.node3164 := by
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
  · exact treeEq3165

def B3170 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq3170 : B3170.tree = HexagonCover.NBand.M6667_6700.SplitData.node3170 := by
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

def B3169 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B3170]
theorem treeEq3169 : B3169.tree = HexagonCover.NBand.M6667_6700.SplitData.node3169 := by
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
  · exact treeEq3170

def B3173 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq3173 : B3173.tree = HexagonCover.NBand.M6667_6700.SplitData.node3173 := by
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

def B3172 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B3173]
theorem treeEq3172 : B3172.tree = HexagonCover.NBand.M6667_6700.SplitData.node3172 := by
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
  · exact treeEq3173

def B3171 : Block := .branch 121 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664091495163455022014509000163419535966272] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B3172, (.leaf 5 (Common.fact 430).pointIds 430), Tip3163_3174]
theorem treeEq3171 : B3171.tree = HexagonCover.NBand.M6667_6700.SplitData.node3171 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3172
  · rfl
  · rfl

def B3168 : Block := .branch 120 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B3169, (.leaf 5 (Common.fact 163).pointIds 163), B3171]
theorem treeEq3168 : B3168.tree = HexagonCover.NBand.M6667_6700.SplitData.node3168 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3169
  · rfl
  · exact treeEq3171

def B3234 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq3234 : B3234.tree = HexagonCover.NBand.M6667_6700.SplitData.node3234 := by
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

def B3233 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B3234]
theorem treeEq3233 : B3233.tree = HexagonCover.NBand.M6667_6700.SplitData.node3233 := by
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
  · exact treeEq3234

def B3237 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq3237 : B3237.tree = HexagonCover.NBand.M6667_6700.SplitData.node3237 := by
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

def B3236 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B3237]
theorem treeEq3236 : B3236.tree = HexagonCover.NBand.M6667_6700.SplitData.node3236 := by
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
  · exact treeEq3237

def B3235 : Block := .branch 121 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664091495163455022014509000163419535966272] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B3236, (.leaf 5 (Common.fact 430).pointIds 430), Tip3163_3238]
theorem treeEq3235 : B3235.tree = HexagonCover.NBand.M6667_6700.SplitData.node3235 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3236
  · rfl
  · rfl

def B3232 : Block := .branch 120 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B3233, (.leaf 5 (Common.fact 163).pointIds 163), B3235]
theorem treeEq3232 : B3232.tree = HexagonCover.NBand.M6667_6700.SplitData.node3232 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3233
  · rfl
  · exact treeEq3235

def B3167 : Block := .branch 47 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 1262).pointIds 1262), B3168, B3232, (.leaf 3 (Common.fact 1263).pointIds 1263), (.leaf 4 (Common.fact 1264).pointIds 1264), (.leaf 5 (Common.fact 1265).pointIds 1265), (.leaf 6 (Common.fact 1273).pointIds 1273)]
theorem treeEq3167 : B3167.tree = HexagonCover.NBand.M6667_6700.SplitData.node3167 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3168
  · exact treeEq3232
  · rfl
  · rfl
  · rfl
  · rfl

def B3166 : Block := .branch 140 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 522673715590561479879743397015195972894736, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3167, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq3166 : B3166.tree = HexagonCover.NBand.M6667_6700.SplitData.node3166 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3167
  · rfl
  · rfl

def B3163 : Block := .branch 119 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B3164, (.leaf 5 (Common.fact 419).pointIds 419), B3166]
theorem treeEq3163 : B3163.tree = HexagonCover.NBand.M6667_6700.SplitData.node3163 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3164
  · rfl
  · exact treeEq3166

theorem accepted3163 : B3163.accepted = true := by decide +kernel
theorem checked3163 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3163 (maskNeeds ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664]) := by
  rw [← treeEq3163]
  exact B3163.sound accepted3163
#print axioms checked3163

def Tip3161_3163 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3163 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] checked3163
def B3301 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq3301 : B3301.tree = HexagonCover.NBand.M6667_6700.SplitData.node3301 := by
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

def B3300 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B3301]
theorem treeEq3300 : B3300.tree = HexagonCover.NBand.M6667_6700.SplitData.node3300 := by
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
  · exact treeEq3301

def B3304 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq3304 : B3304.tree = HexagonCover.NBand.M6667_6700.SplitData.node3304 := by
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

def B3303 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3304]
theorem treeEq3303 : B3303.tree = HexagonCover.NBand.M6667_6700.SplitData.node3303 := by
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
  · exact treeEq3304

def B3302 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3303, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq3302 : B3302.tree = HexagonCover.NBand.M6667_6700.SplitData.node3302 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3303
  · rfl
  · rfl

def B3299 : Block := .branch 119 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B3300, (.leaf 5 (Common.fact 419).pointIds 419), B3302]
theorem treeEq3299 : B3299.tree = HexagonCover.NBand.M6667_6700.SplitData.node3299 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3300
  · rfl
  · exact treeEq3302

def B3306 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq3306 : B3306.tree = HexagonCover.NBand.M6667_6700.SplitData.node3306 := by
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

def B3305 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3306, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq3305 : B3305.tree = HexagonCover.NBand.M6667_6700.SplitData.node3305 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3306
  · rfl
  · rfl

def B3298 : Block := .branch 112 ![385, 1538, 1099511633924, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B3299, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B3305]
theorem treeEq3298 : B3298.tree = HexagonCover.NBand.M6667_6700.SplitData.node3298 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3299
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3305

def B3309 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 5987772208144709258801163742640009936305223892467776] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 1283).pointIds 1283), (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 1284).pointIds 1284)]
theorem treeEq3309 : B3309.tree = HexagonCover.NBand.M6667_6700.SplitData.node3309 := by
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
  · rfl

def B3308 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 5987772208144709258801163742640009936305223892467776] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3309, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1282).pointIds 1282)]
theorem treeEq3308 : B3308.tree = HexagonCover.NBand.M6667_6700.SplitData.node3308 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3309
  · rfl
  · rfl

def B3307 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96718787935653203621732360, 696898287454081973172991196020261297160208, 393248, 5986310706507378355882960057807293653285567959924800] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1279).pointIds 1279), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3308]
theorem treeEq3307 : B3307.tree = HexagonCover.NBand.M6667_6700.SplitData.node3307 := by
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
  · exact treeEq3308

def B3297 : Block := .branch 72 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3298, B3307, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq3297 : B3297.tree = HexagonCover.NBand.M6667_6700.SplitData.node3297 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3298
  · exact treeEq3307
  · rfl
  · rfl
  · rfl

def B3296 : Block := .branch 139 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B3297, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq3296 : B3296.tree = HexagonCover.NBand.M6667_6700.SplitData.node3296 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3297
  · rfl
  · rfl

def B3162 : Block := .branch 111 ![1152921504606847361, 1538, 2398076730681753344004, 96714065569170333976518664, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![Tip3161_3163, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B3296]
theorem treeEq3162 : B3162.tree = HexagonCover.NBand.M6667_6700.SplitData.node3162 := by
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
  · exact treeEq3296

def B3313 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892964684172976562205815952610164800] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1286).pointIds 1286)]
theorem treeEq3313 : B3313.tree = HexagonCover.NBand.M6667_6700.SplitData.node3313 := by
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

def B3312 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598844397538625825299752115148161088] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3313]
theorem treeEq3312 : B3312.tree = HexagonCover.NBand.M6667_6700.SplitData.node3312 := by
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
  · exact treeEq3313

def B3311 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374875169975376600142471753259532206884739230466112] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3312, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1285).pointIds 1285)]
theorem treeEq3311 : B3311.tree = HexagonCover.NBand.M6667_6700.SplitData.node3311 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3312
  · rfl
  · rfl

def B3310 : Block := .branch 159 ![385, 618970609938500496155215362, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374144419156711148683369910843174065374911264194624] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 1269).pointIds 1269), (.leaf 2 (Common.fact 1250).pointIds 1250), (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), B3311]
theorem treeEq3310 : B3310.tree = HexagonCover.NBand.M6667_6700.SplitData.node3310 := by
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
  · exact treeEq3311

def B3161 : Block := .branch 69 ![1152921504606847361, 618970019642690137449563650, 2398076730681753344004, 96714065569170333976518664, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898299126371235985136025664] ![B3162, B3310, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq3161 : B3161.tree = HexagonCover.NBand.M6667_6700.SplitData.node3161 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3162
  · exact treeEq3310
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3161 : B3161.accepted = true := by decide +kernel
theorem checked3161 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3161 (maskNeeds ![1152921504606847361, 618970019642690137449563650, 2398076730681753344004, 96714065569170333976518664, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898299126371235985136025664]) := by
  rw [← treeEq3161]
  exact B3161.sound accepted3161
#print axioms checked3161

def Tip3154_3161 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3161 ![1152921504606847361, 618970019642690137449563650, 2398076730681753344004, 96714065569170333976518664, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898299126371235985136025664] checked3161
def B3160 : Block := .branch 132 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764357729643384042495148096] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq3160 : B3160.tree = HexagonCover.NBand.M6667_6700.SplitData.node3160 := by
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

def B3159 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387130006992737320205033144384] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B3160]
theorem treeEq3159 : B3159.tree = HexagonCover.NBand.M6667_6700.SplitData.node3159 := by
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
  · exact treeEq3160

def B3158 : Block := .branch 108 ![1152921504606847361, 618970019642690137449563650, 2398076730681753344004, 96714065569170333976518664, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B3159, (.leaf 5 (Common.fact 136).pointIds 136), Tip3154_3161]
theorem treeEq3158 : B3158.tree = HexagonCover.NBand.M6667_6700.SplitData.node3158 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3159
  · rfl
  · rfl

def B3316 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240258071987486287549956160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 957).pointIds 957)]
theorem treeEq3316 : B3316.tree = HexagonCover.NBand.M6667_6700.SplitData.node3316 := by
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

def B3315 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605907335081422450087952448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3316]
theorem treeEq3315 : B3315.tree = HexagonCover.NBand.M6667_6700.SplitData.node3315 := by
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
  · exact treeEq3316

def B3314 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820541041988555074170257472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3315, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq3314 : B3314.tree = HexagonCover.NBand.M6667_6700.SplitData.node3314 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3315
  · rfl
  · rfl

def B3157 : Block := .branch 101 ![1152921504606847361, 618970019642690137449563650, 2398076730681753344004, 96714065569170333976518664, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![B3158, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B3314]
theorem treeEq3157 : B3157.tree = HexagonCover.NBand.M6667_6700.SplitData.node3157 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3158
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3314

def B3319 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180749340131798850933144245764160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq3319 : B3319.tree = HexagonCover.NBand.M6667_6700.SplitData.node3319 := by
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

def B3318 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060462705781061944869306783760448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3319]
theorem treeEq3318 : B3318.tree = HexagonCover.NBand.M6667_6700.SplitData.node3318 := by
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
  · exact treeEq3319

def B3317 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358536920414768852001930866065472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3318, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 958).pointIds 958)]
theorem treeEq3317 : B3317.tree = HexagonCover.NBand.M6667_6700.SplitData.node3317 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3318
  · rfl
  · rfl

def B3156 : Block := .branch 91 ![1152921504606847361, 618970019642690137449563650, 2398076730681753344004, 96714065569170333976518664, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![B3157, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B3317]
theorem treeEq3156 : B3156.tree = HexagonCover.NBand.M6667_6700.SplitData.node3156 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3157
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3317

def B3322 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040558027635171373431593107520] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3322 : B3322.tree = HexagonCover.NBand.M6667_6700.SplitData.node3322 := by
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

def B3321 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923676898265309594131103808] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3322]
theorem treeEq3321 : B3321.tree = HexagonCover.NBand.M6667_6700.SplitData.node3321 := by
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
  · exact treeEq3322

def B3320 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138310605172442218213408832] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3321, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq3320 : B3320.tree = HexagonCover.NBand.M6667_6700.SplitData.node3320 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3321
  · rfl
  · rfl

def B3155 : Block := .branch 89 ![1152921504606847361, 1538, 2398076730681753344004, 96714065569170333976518664, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 117).pointIds 117), B3156, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B3320]
theorem treeEq3155 : B3155.tree = HexagonCover.NBand.M6667_6700.SplitData.node3155 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3156
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3320

def B3325 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929078925041369935500542016] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq3325 : B3325.tree = HexagonCover.NBand.M6667_6700.SplitData.node3325 := by
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

def B3324 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294728188135306098038538304] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3325]
theorem treeEq3324 : B3324.tree = HexagonCover.NBand.M6667_6700.SplitData.node3324 := by
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
  · exact treeEq3325

def B3323 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461422011952099789096296644672] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3324, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq3323 : B3323.tree = HexagonCover.NBand.M6667_6700.SplitData.node3323 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3324
  · rfl
  · rfl

def B3154 : Block := .branch 86 ![1152921504606847361, 1538, 2398076730681753344004, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B3155, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B3323]
theorem treeEq3154 : B3154.tree = HexagonCover.NBand.M6667_6700.SplitData.node3154 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3155
  · rfl
  · rfl
  · exact treeEq3323

theorem accepted3154 : B3154.accepted = true := by decide +kernel
theorem checked3154 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3154 (maskNeeds ![1152921504606847361, 1538, 2398076730681753344004, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq3154]
  exact B3154.sound accepted3154
#print axioms checked3154

end HexagonCover.NBand.M6667_6700.SplitTree.Run0045
