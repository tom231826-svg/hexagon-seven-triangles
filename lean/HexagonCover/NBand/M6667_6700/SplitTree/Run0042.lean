import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0041
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0042
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3018_3019 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3019 ![5319508131568930906582414993892835713, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] HexagonCover.NBand.M6667_6700.SplitTree.Run0041.checked3019
def B3043 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3043 : B3043.tree = HexagonCover.NBand.M6667_6700.SplitData.node3043 := by
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

def B3042 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3043]
theorem treeEq3042 : B3042.tree = HexagonCover.NBand.M6667_6700.SplitData.node3042 := by
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
  · exact treeEq3043

def B3045 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq3045 : B3045.tree = HexagonCover.NBand.M6667_6700.SplitData.node3045 := by
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

def B3044 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3045, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3044 : B3044.tree = HexagonCover.NBand.M6667_6700.SplitData.node3044 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3045
  · rfl
  · rfl

def B3041 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3042, (.leaf 5 (Common.fact 439).pointIds 439), B3044]
theorem treeEq3041 : B3041.tree = HexagonCover.NBand.M6667_6700.SplitData.node3041 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3042
  · rfl
  · exact treeEq3044

def B3047 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3047 : B3047.tree = HexagonCover.NBand.M6667_6700.SplitData.node3047 := by
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

def B3046 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3047]
theorem treeEq3046 : B3046.tree = HexagonCover.NBand.M6667_6700.SplitData.node3046 := by
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
  · exact treeEq3047

def B3040 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376686569847858686053580864] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3041, B3046, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3040 : B3040.tree = HexagonCover.NBand.M6667_6700.SplitData.node3040 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3041
  · exact treeEq3046
  · rfl
  · rfl

def B3050 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894347817055727507503317056] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3050 : B3050.tree = HexagonCover.NBand.M6667_6700.SplitData.node3050 := by
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

def B3049 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053356944869431472157655302208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3050]
theorem treeEq3049 : B3049.tree = HexagonCover.NBand.M6667_6700.SplitData.node3049 := by
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
  · exact treeEq3050

def B3048 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818557646125237003065387937758183488] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3049, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3048 : B3048.tree = HexagonCover.NBand.M6667_6700.SplitData.node3048 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3049
  · rfl
  · rfl

def B3039 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3040, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3048, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3039 : B3039.tree = HexagonCover.NBand.M6667_6700.SplitData.node3039 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3040
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3048
  · rfl

def B3053 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3053 : B3053.tree = HexagonCover.NBand.M6667_6700.SplitData.node3053 := by
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

def B3052 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3053]
theorem treeEq3052 : B3052.tree = HexagonCover.NBand.M6667_6700.SplitData.node3052 := by
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
  · exact treeEq3053

def B3051 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3052, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3051 : B3051.tree = HexagonCover.NBand.M6667_6700.SplitData.node3051 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3052
  · rfl
  · rfl

def B3038 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3039, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3051]
theorem treeEq3038 : B3038.tree = HexagonCover.NBand.M6667_6700.SplitData.node3038 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3039
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3051

def B3037 : Block := .branch 140 ![385, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3038, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq3037 : B3037.tree = HexagonCover.NBand.M6667_6700.SplitData.node3037 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3038
  · rfl
  · rfl

def B3018 : Block := .branch 122 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![Tip3018_3019, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B3037]
theorem treeEq3018 : B3018.tree = HexagonCover.NBand.M6667_6700.SplitData.node3018 := by
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
  · exact treeEq3037

theorem accepted3018 : B3018.accepted = true := by decide +kernel
theorem checked3018 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3018 (maskNeeds ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968]) := by
  rw [← treeEq3018]
  exact B3018.sound accepted3018
#print axioms checked3018

def B3068 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3068 : B3068.tree = HexagonCover.NBand.M6667_6700.SplitData.node3068 := by
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

def B3067 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3068]
theorem treeEq3067 : B3067.tree = HexagonCover.NBand.M6667_6700.SplitData.node3067 := by
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
  · exact treeEq3068

def B3070 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq3070 : B3070.tree = HexagonCover.NBand.M6667_6700.SplitData.node3070 := by
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

def B3069 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3070, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3069 : B3069.tree = HexagonCover.NBand.M6667_6700.SplitData.node3069 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3070
  · rfl
  · rfl

def B3066 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3067, (.leaf 5 (Common.fact 439).pointIds 439), B3069]
theorem treeEq3066 : B3066.tree = HexagonCover.NBand.M6667_6700.SplitData.node3066 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3067
  · rfl
  · exact treeEq3069

def B3072 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3072 : B3072.tree = HexagonCover.NBand.M6667_6700.SplitData.node3072 := by
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

def B3071 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3072]
theorem treeEq3071 : B3071.tree = HexagonCover.NBand.M6667_6700.SplitData.node3071 := by
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
  · exact treeEq3072

def B3065 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715684808496787692392546368] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3066, B3071, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3065 : B3065.tree = HexagonCover.NBand.M6667_6700.SplitData.node3065 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3066
  · exact treeEq3071
  · rfl
  · rfl

def B3075 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233346055704656513842282560] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3075 : B3075.tree = HexagonCover.NBand.M6667_6700.SplitData.node3075 := by
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

def B3074 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699695943108080401163994267712] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3075]
theorem treeEq3074 : B3074.tree = HexagonCover.NBand.M6667_6700.SplitData.node3074 := by
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
  · exact treeEq3075

def B3073 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724991292464235241714316944097148992] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3074, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3073 : B3073.tree = HexagonCover.NBand.M6667_6700.SplitData.node3073 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3074
  · rfl
  · rfl

def B3064 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3065, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3073, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3064 : B3064.tree = HexagonCover.NBand.M6667_6700.SplitData.node3064 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3065
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3073
  · rfl

def B3078 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3078 : B3078.tree = HexagonCover.NBand.M6667_6700.SplitData.node3078 := by
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

def B3077 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3078]
theorem treeEq3077 : B3077.tree = HexagonCover.NBand.M6667_6700.SplitData.node3077 := by
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
  · exact treeEq3078

def B3076 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3077, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3076 : B3076.tree = HexagonCover.NBand.M6667_6700.SplitData.node3076 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3077
  · rfl
  · rfl

def B3063 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3064, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3076]
theorem treeEq3063 : B3063.tree = HexagonCover.NBand.M6667_6700.SplitData.node3063 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3064
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3076

def B3062 : Block := .branch 140 ![385, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3063, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq3062 : B3062.tree = HexagonCover.NBand.M6667_6700.SplitData.node3062 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3063
  · rfl
  · rfl

def B3061 : Block := .branch 163 ![5319508131568930906582414993892835713, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B3062]
theorem treeEq3061 : B3061.tree = HexagonCover.NBand.M6667_6700.SplitData.node3061 := by
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
  · exact treeEq3062

theorem accepted3061 : B3061.accepted = true := by decide +kernel
theorem checked3061 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3061 (maskNeeds ![5319508131568930906582414993892835713, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968]) := by
  rw [← treeEq3061]
  exact B3061.sound accepted3061
#print axioms checked3061

def Tip3060_3061 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3061 ![5319508131568930906582414993892835713, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] checked3061
def B3085 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3085 : B3085.tree = HexagonCover.NBand.M6667_6700.SplitData.node3085 := by
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

def B3084 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3085]
theorem treeEq3084 : B3084.tree = HexagonCover.NBand.M6667_6700.SplitData.node3084 := by
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
  · exact treeEq3085

def B3087 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq3087 : B3087.tree = HexagonCover.NBand.M6667_6700.SplitData.node3087 := by
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

def B3086 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3087, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3086 : B3086.tree = HexagonCover.NBand.M6667_6700.SplitData.node3086 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3087
  · rfl
  · rfl

def B3083 : Block := .branch 128 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B3084, (.leaf 5 (Common.fact 439).pointIds 439), B3086]
theorem treeEq3083 : B3083.tree = HexagonCover.NBand.M6667_6700.SplitData.node3083 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3084
  · rfl
  · exact treeEq3086

def B3089 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3089 : B3089.tree = HexagonCover.NBand.M6667_6700.SplitData.node3089 := by
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

def B3088 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3089]
theorem treeEq3088 : B3088.tree = HexagonCover.NBand.M6667_6700.SplitData.node3088 := by
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
  · exact treeEq3089

def B3082 : Block := .branch 127 ![385, 1538, 1099511633924, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376686569847858686053580864] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3083, B3088, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3082 : B3082.tree = HexagonCover.NBand.M6667_6700.SplitData.node3082 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3083
  · exact treeEq3088
  · rfl
  · rfl

def B3092 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894347817055727507503317056] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3092 : B3092.tree = HexagonCover.NBand.M6667_6700.SplitData.node3092 := by
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

def B3091 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053356944869431472157655302208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3092]
theorem treeEq3091 : B3091.tree = HexagonCover.NBand.M6667_6700.SplitData.node3091 := by
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
  · exact treeEq3092

def B3090 : Block := .branch 167 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818557646125237003065387937758183488] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3091, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3090 : B3090.tree = HexagonCover.NBand.M6667_6700.SplitData.node3090 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3091
  · rfl
  · rfl

def B3081 : Block := .branch 125 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3082, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3090, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3081 : B3081.tree = HexagonCover.NBand.M6667_6700.SplitData.node3081 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3082
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3090
  · rfl

def B3095 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3095 : B3095.tree = HexagonCover.NBand.M6667_6700.SplitData.node3095 := by
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

def B3094 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3095]
theorem treeEq3094 : B3094.tree = HexagonCover.NBand.M6667_6700.SplitData.node3094 := by
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
  · exact treeEq3095

def B3093 : Block := .branch 169 ![385, 1538, 1099511633924, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3094, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3093 : B3093.tree = HexagonCover.NBand.M6667_6700.SplitData.node3093 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3094
  · rfl
  · rfl

def B3080 : Block := .branch 123 ![385, 1538, 1099511633924, 19342813113834066795323400, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3081, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3093]
theorem treeEq3080 : B3080.tree = HexagonCover.NBand.M6667_6700.SplitData.node3080 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3081
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3093

def B3079 : Block := .branch 140 ![385, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3080, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq3079 : B3079.tree = HexagonCover.NBand.M6667_6700.SplitData.node3079 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3080
  · rfl
  · rfl

def B3060 : Block := .branch 122 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![Tip3060_3061, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B3079]
theorem treeEq3060 : B3060.tree = HexagonCover.NBand.M6667_6700.SplitData.node3060 := by
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
  · exact treeEq3079

theorem accepted3060 : B3060.accepted = true := by decide +kernel
theorem checked3060 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3060 (maskNeeds ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968]) := by
  rw [← treeEq3060]
  exact B3060.sound accepted3060
#print axioms checked3060

def Tip3008_3018 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3018 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] checked3018
def Tip3008_3060 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3060 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] checked3060
def B3010 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq3010 : B3010.tree = HexagonCover.NBand.M6667_6700.SplitData.node3010 := by
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

def B3009 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B3010]
theorem treeEq3009 : B3009.tree = HexagonCover.NBand.M6667_6700.SplitData.node3009 := by
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
  · exact treeEq3010

def B3014 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq3014 : B3014.tree = HexagonCover.NBand.M6667_6700.SplitData.node3014 := by
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

def B3013 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B3014]
theorem treeEq3013 : B3013.tree = HexagonCover.NBand.M6667_6700.SplitData.node3013 := by
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
  · exact treeEq3014

def B3017 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq3017 : B3017.tree = HexagonCover.NBand.M6667_6700.SplitData.node3017 := by
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

def B3016 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B3017]
theorem treeEq3016 : B3016.tree = HexagonCover.NBand.M6667_6700.SplitData.node3016 := by
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
  · exact treeEq3017

def B3015 : Block := .branch 121 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664091495487973575597377863220661233123392] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B3016, (.leaf 5 (Common.fact 430).pointIds 430), Tip3008_3018]
theorem treeEq3015 : B3015.tree = HexagonCover.NBand.M6667_6700.SplitData.node3015 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3016
  · rfl
  · rfl

def B3012 : Block := .branch 120 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664090166259977790681504959413600952778816] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B3013, (.leaf 5 (Common.fact 163).pointIds 163), B3015]
theorem treeEq3012 : B3012.tree = HexagonCover.NBand.M6667_6700.SplitData.node3012 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3013
  · rfl
  · exact treeEq3015

def B3056 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq3056 : B3056.tree = HexagonCover.NBand.M6667_6700.SplitData.node3056 := by
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

def B3055 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B3056]
theorem treeEq3055 : B3055.tree = HexagonCover.NBand.M6667_6700.SplitData.node3055 := by
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
  · exact treeEq3056

def B3059 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq3059 : B3059.tree = HexagonCover.NBand.M6667_6700.SplitData.node3059 := by
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

def B3058 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B3059]
theorem treeEq3058 : B3058.tree = HexagonCover.NBand.M6667_6700.SplitData.node3058 := by
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
  · exact treeEq3059

def B3057 : Block := .branch 121 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664091495487973575597377863220661233123392] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B3058, (.leaf 5 (Common.fact 430).pointIds 430), Tip3008_3060]
theorem treeEq3057 : B3057.tree = HexagonCover.NBand.M6667_6700.SplitData.node3057 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3058
  · rfl
  · rfl

def B3054 : Block := .branch 120 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664090166259977790681504959413600952778816] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B3055, (.leaf 5 (Common.fact 163).pointIds 163), B3057]
theorem treeEq3054 : B3054.tree = HexagonCover.NBand.M6667_6700.SplitData.node3054 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3055
  · rfl
  · exact treeEq3057

def B3011 : Block := .branch 47 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664090166259977790681504959413600952778816] ![(.leaf 0 (Common.fact 1262).pointIds 1262), B3012, B3054, (.leaf 3 (Common.fact 1263).pointIds 1263), (.leaf 4 (Common.fact 1264).pointIds 1264), (.leaf 5 (Common.fact 1265).pointIds 1265), (.leaf 6 (Common.fact 1266).pointIds 1266)]
theorem treeEq3011 : B3011.tree = HexagonCover.NBand.M6667_6700.SplitData.node3011 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3012
  · exact treeEq3054
  · rfl
  · rfl
  · rfl
  · rfl

def B3008 : Block := .branch 119 ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898223568507510070812606528] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B3009, (.leaf 5 (Common.fact 419).pointIds 419), B3011]
theorem treeEq3008 : B3008.tree = HexagonCover.NBand.M6667_6700.SplitData.node3008 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3009
  · rfl
  · exact treeEq3011

theorem accepted3008 : B3008.accepted = true := by decide +kernel
theorem checked3008 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3008 (maskNeeds ![2596148429267414967186752771457409, 1538, 1099511633924, 19342813113834066795323400, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898223568507510070812606528]) := by
  rw [← treeEq3008]
  exact B3008.sound accepted3008
#print axioms checked3008

end HexagonCover.NBand.M6667_6700.SplitTree.Run0042
