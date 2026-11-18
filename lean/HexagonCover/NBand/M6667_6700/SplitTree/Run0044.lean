import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0043
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0044
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B3212 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq3212 : B3212.tree = HexagonCover.NBand.M6667_6700.SplitData.node3212 := by
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

def B3211 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3212]
theorem treeEq3211 : B3211.tree = HexagonCover.NBand.M6667_6700.SplitData.node3211 := by
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
  · exact treeEq3212

def B3214 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq3214 : B3214.tree = HexagonCover.NBand.M6667_6700.SplitData.node3214 := by
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

def B3213 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3214, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq3213 : B3213.tree = HexagonCover.NBand.M6667_6700.SplitData.node3213 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3214
  · rfl
  · rfl

def B3210 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3211, (.leaf 5 (Common.fact 439).pointIds 439), B3213]
theorem treeEq3210 : B3210.tree = HexagonCover.NBand.M6667_6700.SplitData.node3210 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3211
  · rfl
  · exact treeEq3213

def B3216 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq3216 : B3216.tree = HexagonCover.NBand.M6667_6700.SplitData.node3216 := by
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

def B3215 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3216]
theorem treeEq3215 : B3215.tree = HexagonCover.NBand.M6667_6700.SplitData.node3215 := by
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
  · exact treeEq3216

def B3209 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3210, B3215, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3209 : B3209.tree = HexagonCover.NBand.M6667_6700.SplitData.node3209 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3210
  · exact treeEq3215
  · rfl
  · rfl

def B3219 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq3219 : B3219.tree = HexagonCover.NBand.M6667_6700.SplitData.node3219 := by
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

def B3218 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3219]
theorem treeEq3218 : B3218.tree = HexagonCover.NBand.M6667_6700.SplitData.node3218 := by
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
  · exact treeEq3219

def B3217 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3218, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3217 : B3217.tree = HexagonCover.NBand.M6667_6700.SplitData.node3217 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3218
  · rfl
  · rfl

def B3208 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B3209, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3217, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3208 : B3208.tree = HexagonCover.NBand.M6667_6700.SplitData.node3208 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3209
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3217
  · rfl

def B3222 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq3222 : B3222.tree = HexagonCover.NBand.M6667_6700.SplitData.node3222 := by
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

def B3221 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3222]
theorem treeEq3221 : B3221.tree = HexagonCover.NBand.M6667_6700.SplitData.node3221 := by
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
  · exact treeEq3222

def B3220 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3221, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq3220 : B3220.tree = HexagonCover.NBand.M6667_6700.SplitData.node3220 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3221
  · rfl
  · rfl

def B3207 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B3208, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3220]
theorem treeEq3207 : B3207.tree = HexagonCover.NBand.M6667_6700.SplitData.node3207 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3208
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3220

def B3225 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1281).pointIds 1281)]
theorem treeEq3225 : B3225.tree = HexagonCover.NBand.M6667_6700.SplitData.node3225 := by
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

def B3224 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3225, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1280).pointIds 1280)]
theorem treeEq3224 : B3224.tree = HexagonCover.NBand.M6667_6700.SplitData.node3224 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3225
  · rfl
  · rfl

def B3223 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96732955035101812557373448, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502134741101683803948580928] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1275).pointIds 1275), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3224]
theorem treeEq3223 : B3223.tree = HexagonCover.NBand.M6667_6700.SplitData.node3223 := by
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
  · exact treeEq3224

def B3206 : Block := .branch 74 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B3207, B3223, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3206 : B3206.tree = HexagonCover.NBand.M6667_6700.SplitData.node3206 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3207
  · exact treeEq3223
  · rfl
  · rfl
  · rfl

theorem accepted3206 : B3206.accepted = true := by decide +kernel
theorem checked3206 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3206 (maskNeeds ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152]) := by
  rw [← treeEq3206]
  exact B3206.sound accepted3206
#print axioms checked3206

def Tip3174_3178 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3178 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] HexagonCover.NBand.M6667_6700.SplitTree.Run0043.checked3178
def Tip3174_3206 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3206 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] checked3206
def B3200 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1277).pointIds 1277)]
theorem treeEq3200 : B3200.tree = HexagonCover.NBand.M6667_6700.SplitData.node3200 := by
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

def B3199 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3200, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1276).pointIds 1276)]
theorem treeEq3199 : B3199.tree = HexagonCover.NBand.M6667_6700.SplitData.node3199 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3200
  · rfl
  · rfl

def B3198 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96723510302136073266946056, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841132979750612810287546432] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1278).pointIds 1278), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3199]
theorem treeEq3198 : B3198.tree = HexagonCover.NBand.M6667_6700.SplitData.node3198 := by
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
  · exact treeEq3199

def B3177 : Block := .branch 73 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip3174_3178, B3198, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3177 : B3177.tree = HexagonCover.NBand.M6667_6700.SplitData.node3177 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3198
  · rfl
  · rfl
  · rfl

def B3203 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1277).pointIds 1277)]
theorem treeEq3203 : B3203.tree = HexagonCover.NBand.M6667_6700.SplitData.node3203 := by
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

def B3202 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3203, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1276).pointIds 1276)]
theorem treeEq3202 : B3202.tree = HexagonCover.NBand.M6667_6700.SplitData.node3202 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3203
  · rfl
  · rfl

def B3201 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96718787935653203621732360, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841132979750612810287546432] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1279).pointIds 1279), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3202]
theorem treeEq3201 : B3201.tree = HexagonCover.NBand.M6667_6700.SplitData.node3201 := by
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
  · exact treeEq3202

def B3176 : Block := .branch 72 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3177, B3201, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 915).pointIds 915)]
theorem treeEq3176 : B3176.tree = HexagonCover.NBand.M6667_6700.SplitData.node3176 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3177
  · exact treeEq3201
  · rfl
  · rfl
  · rfl

def B3175 : Block := .branch 163 ![5319508131568930906582414993892835713, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B3176]
theorem treeEq3175 : B3175.tree = HexagonCover.NBand.M6667_6700.SplitData.node3175 := by
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
  · exact treeEq3176

def B3228 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1281).pointIds 1281)]
theorem treeEq3228 : B3228.tree = HexagonCover.NBand.M6667_6700.SplitData.node3228 := by
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

def B3227 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3228, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1280).pointIds 1280)]
theorem treeEq3227 : B3227.tree = HexagonCover.NBand.M6667_6700.SplitData.node3227 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3228
  · rfl
  · rfl

def B3226 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96723510302136073266946056, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502134741101683803948580928] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1278).pointIds 1278), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3227]
theorem treeEq3226 : B3226.tree = HexagonCover.NBand.M6667_6700.SplitData.node3226 := by
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
  · exact treeEq3227

def B3205 : Block := .branch 73 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip3174_3206, B3226, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq3205 : B3205.tree = HexagonCover.NBand.M6667_6700.SplitData.node3205 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3226
  · rfl
  · rfl
  · rfl

def B3231 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1281).pointIds 1281)]
theorem treeEq3231 : B3231.tree = HexagonCover.NBand.M6667_6700.SplitData.node3231 := by
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

def B3230 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3231, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1280).pointIds 1280)]
theorem treeEq3230 : B3230.tree = HexagonCover.NBand.M6667_6700.SplitData.node3230 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3231
  · rfl
  · rfl

def B3229 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96718787935653203621732360, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502134741101683803948580928] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1279).pointIds 1279), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3230]
theorem treeEq3229 : B3229.tree = HexagonCover.NBand.M6667_6700.SplitData.node3229 := by
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
  · exact treeEq3230

def B3204 : Block := .branch 72 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3205, B3229, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq3204 : B3204.tree = HexagonCover.NBand.M6667_6700.SplitData.node3204 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3205
  · exact treeEq3229
  · rfl
  · rfl
  · rfl

def B3174 : Block := .branch 122 ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] ![B3175, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B3204]
theorem treeEq3174 : B3174.tree = HexagonCover.NBand.M6667_6700.SplitData.node3174 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3175
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3204

theorem accepted3174 : B3174.accepted = true := by decide +kernel
theorem checked3174 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3174 (maskNeeds ![2596148429267414967186752771457409, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848]) := by
  rw [← treeEq3174]
  exact B3174.sound accepted3174
#print axioms checked3174

def B3248 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3248 : B3248.tree = HexagonCover.NBand.M6667_6700.SplitData.node3248 := by
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

def B3247 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3248]
theorem treeEq3247 : B3247.tree = HexagonCover.NBand.M6667_6700.SplitData.node3247 := by
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
  · exact treeEq3248

def B3250 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq3250 : B3250.tree = HexagonCover.NBand.M6667_6700.SplitData.node3250 := by
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

def B3249 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3250, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3249 : B3249.tree = HexagonCover.NBand.M6667_6700.SplitData.node3249 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3250
  · rfl
  · rfl

def B3246 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3247, (.leaf 5 (Common.fact 439).pointIds 439), B3249]
theorem treeEq3246 : B3246.tree = HexagonCover.NBand.M6667_6700.SplitData.node3246 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3247
  · rfl
  · exact treeEq3249

def B3252 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq3252 : B3252.tree = HexagonCover.NBand.M6667_6700.SplitData.node3252 := by
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

def B3251 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3252]
theorem treeEq3251 : B3251.tree = HexagonCover.NBand.M6667_6700.SplitData.node3251 := by
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
  · exact treeEq3252

def B3245 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3246, B3251, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3245 : B3245.tree = HexagonCover.NBand.M6667_6700.SplitData.node3245 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3246
  · exact treeEq3251
  · rfl
  · rfl

def B3255 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3255 : B3255.tree = HexagonCover.NBand.M6667_6700.SplitData.node3255 := by
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

def B3254 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3255]
theorem treeEq3254 : B3254.tree = HexagonCover.NBand.M6667_6700.SplitData.node3254 := by
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
  · exact treeEq3255

def B3253 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3254, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3253 : B3253.tree = HexagonCover.NBand.M6667_6700.SplitData.node3253 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3254
  · rfl
  · rfl

def B3244 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3245, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3253, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3244 : B3244.tree = HexagonCover.NBand.M6667_6700.SplitData.node3244 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3245
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3253
  · rfl

def B3258 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq3258 : B3258.tree = HexagonCover.NBand.M6667_6700.SplitData.node3258 := by
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

def B3257 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3258]
theorem treeEq3257 : B3257.tree = HexagonCover.NBand.M6667_6700.SplitData.node3257 := by
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
  · exact treeEq3258

def B3256 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3257, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq3256 : B3256.tree = HexagonCover.NBand.M6667_6700.SplitData.node3256 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3257
  · rfl
  · rfl

def B3243 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B3244, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3256]
theorem treeEq3243 : B3243.tree = HexagonCover.NBand.M6667_6700.SplitData.node3243 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3244
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3256

def B3261 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1277).pointIds 1277)]
theorem treeEq3261 : B3261.tree = HexagonCover.NBand.M6667_6700.SplitData.node3261 := by
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

def B3260 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5999464221243359802296749525965696033632466220089408] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3261, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1276).pointIds 1276)]
theorem treeEq3260 : B3260.tree = HexagonCover.NBand.M6667_6700.SplitData.node3260 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3261
  · rfl
  · rfl

def B3259 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96732955035101812557373448, 1393796574908163946345982392040522594222096, 393248, 5998002719606028899378545841132979750612810287546432] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1275).pointIds 1275), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3260]
theorem treeEq3259 : B3259.tree = HexagonCover.NBand.M6667_6700.SplitData.node3259 := by
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
  · exact treeEq3260

def B3242 : Block := .branch 74 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B3243, B3259, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq3242 : B3242.tree = HexagonCover.NBand.M6667_6700.SplitData.node3242 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3243
  · exact treeEq3259
  · rfl
  · rfl
  · rfl

theorem accepted3242 : B3242.accepted = true := by decide +kernel
theorem checked3242 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3242 (maskNeeds ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656]) := by
  rw [← treeEq3242]
  exact B3242.sound accepted3242
#print axioms checked3242

def B3276 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq3276 : B3276.tree = HexagonCover.NBand.M6667_6700.SplitData.node3276 := by
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

def B3275 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3276]
theorem treeEq3275 : B3275.tree = HexagonCover.NBand.M6667_6700.SplitData.node3275 := by
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
  · exact treeEq3276

def B3278 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq3278 : B3278.tree = HexagonCover.NBand.M6667_6700.SplitData.node3278 := by
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

def B3277 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3278, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq3277 : B3277.tree = HexagonCover.NBand.M6667_6700.SplitData.node3277 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3278
  · rfl
  · rfl

def B3274 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3275, (.leaf 5 (Common.fact 439).pointIds 439), B3277]
theorem treeEq3274 : B3274.tree = HexagonCover.NBand.M6667_6700.SplitData.node3274 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3275
  · rfl
  · exact treeEq3277

def B3280 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq3280 : B3280.tree = HexagonCover.NBand.M6667_6700.SplitData.node3280 := by
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

def B3279 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3280]
theorem treeEq3279 : B3279.tree = HexagonCover.NBand.M6667_6700.SplitData.node3279 := by
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
  · exact treeEq3280

def B3273 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3274, B3279, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3273 : B3273.tree = HexagonCover.NBand.M6667_6700.SplitData.node3273 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3274
  · exact treeEq3279
  · rfl
  · rfl

def B3283 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq3283 : B3283.tree = HexagonCover.NBand.M6667_6700.SplitData.node3283 := by
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

def B3282 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3283]
theorem treeEq3282 : B3282.tree = HexagonCover.NBand.M6667_6700.SplitData.node3282 := by
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
  · exact treeEq3283

def B3281 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3282, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3281 : B3281.tree = HexagonCover.NBand.M6667_6700.SplitData.node3281 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3282
  · rfl
  · rfl

def B3272 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B3273, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3281, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3272 : B3272.tree = HexagonCover.NBand.M6667_6700.SplitData.node3272 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3273
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3281
  · rfl

def B3286 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq3286 : B3286.tree = HexagonCover.NBand.M6667_6700.SplitData.node3286 := by
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

def B3285 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3286]
theorem treeEq3285 : B3285.tree = HexagonCover.NBand.M6667_6700.SplitData.node3285 := by
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
  · exact treeEq3286

def B3284 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3285, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq3284 : B3284.tree = HexagonCover.NBand.M6667_6700.SplitData.node3284 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3285
  · rfl
  · rfl

def B3271 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B3272, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3284]
theorem treeEq3271 : B3271.tree = HexagonCover.NBand.M6667_6700.SplitData.node3271 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3272
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3284

def B3289 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1281).pointIds 1281)]
theorem treeEq3289 : B3289.tree = HexagonCover.NBand.M6667_6700.SplitData.node3289 := by
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

def B3288 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 5987772208144717895863103186967457384703459881123904] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3289, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1280).pointIds 1280)]
theorem treeEq3288 : B3288.tree = HexagonCover.NBand.M6667_6700.SplitData.node3288 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3289
  · rfl
  · rfl

def B3287 : Block := .branch 160 ![385, 1538, 2398076730681753344004, 96732955035101812557373448, 1393796574908163946345982392040522594222096, 393248, 5986310706507386992944899502134741101683803948580928] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1274).pointIds 1274), (.leaf 3 (Common.fact 1275).pointIds 1275), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3288]
theorem treeEq3287 : B3287.tree = HexagonCover.NBand.M6667_6700.SplitData.node3287 := by
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
  · exact treeEq3288

def B3270 : Block := .branch 74 ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B3271, B3287, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3270 : B3270.tree = HexagonCover.NBand.M6667_6700.SplitData.node3270 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3271
  · exact treeEq3287
  · rfl
  · rfl
  · rfl

theorem accepted3270 : B3270.accepted = true := by decide +kernel
theorem checked3270 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3270 (maskNeeds ![385, 1538, 2398076730681753344004, 96714065569170333976518664, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152]) := by
  rw [← treeEq3270]
  exact B3270.sound accepted3270
#print axioms checked3270

end HexagonCover.NBand.M6667_6700.SplitTree.Run0044
