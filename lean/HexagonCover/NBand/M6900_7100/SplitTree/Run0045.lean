import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0044
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0045
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3258_3260 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3260 ![10384593717069655257060992658440577, 148366586124093621762, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0044.checked3260
def B3351 : Block := .branch 161 ![385, 1538, 18446745173221185540, 38695070960633872881049608, 98320, 393248, 7108743963999289865625663087993656582482638809858112] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1139).pointIds 1139)]
theorem treeEq3351 : B3351.tree = HexagonCover.NBand.M6900_7100.SplitData.node3351 := by
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
  · rfl

def B3350 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648518346341352962, 18446745173221185540, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505376453642919676418801347854400] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1189).pointIds 1189), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3351]
theorem treeEq3350 : B3350.tree = HexagonCover.NBand.M6900_7100.SplitData.node3350 := by
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
  · exact treeEq3351

def B3349 : Block := .branch 171 ![385, 792633534417208834, 18446745173221185540, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 6360455125685867571505376763127929497763870072635456] ![B3350, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq3349 : B3349.tree = HexagonCover.NBand.M6900_7100.SplitData.node3349 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3350
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3348 : Block := .branch 151 ![385, 792633534417208834, 18446745173221185540, 38695070960633872881049608, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3349, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3348 : B3348.tree = HexagonCover.NBand.M6900_7100.SplitData.node3348 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3349
  · rfl

def B3347 : Block := .branch 170 ![385, 792633534417208834, 18446745173221185540, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3348, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq3347 : B3347.tree = HexagonCover.NBand.M6900_7100.SplitData.node3347 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3348
  · rfl
  · rfl

def B3346 : Block := .branch 172 ![385, 792633534417208834, 18446745173221185540, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3347]
theorem treeEq3346 : B3346.tree = HexagonCover.NBand.M6900_7100.SplitData.node3346 := by
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
  · exact treeEq3347

def B3259 : Block := .branch 73 ![10384593717069655257060992658440577, 148366586124093621762, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), Tip3258_3260, B3346, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq3259 : B3259.tree = HexagonCover.NBand.M6900_7100.SplitData.node3259 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3346
  · rfl
  · rfl
  · rfl

def B3357 : Block := .branch 161 ![385, 1538, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 7108743963999289865625663087993656582482638809858112] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1139).pointIds 1139)]
theorem treeEq3357 : B3357.tree = HexagonCover.NBand.M6900_7100.SplitData.node3357 := by
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
  · rfl

def B3356 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648518346341352962, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505376453642919676418801347854400] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1189).pointIds 1189), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3357]
theorem treeEq3356 : B3356.tree = HexagonCover.NBand.M6900_7100.SplitData.node3356 := by
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
  · exact treeEq3357

def B3355 : Block := .branch 171 ![385, 792633534417208834, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 6360455125685867571505376763127929497763870072635456] ![B3356, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq3355 : B3355.tree = HexagonCover.NBand.M6900_7100.SplitData.node3355 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3356
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3354 : Block := .branch 151 ![385, 792633534417208834, 18446745173221185540, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3355, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3354 : B3354.tree = HexagonCover.NBand.M6900_7100.SplitData.node3354 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3355
  · rfl

def B3353 : Block := .branch 170 ![385, 792633534417208834, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3354, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq3353 : B3353.tree = HexagonCover.NBand.M6900_7100.SplitData.node3353 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3354
  · rfl
  · rfl

def B3352 : Block := .branch 172 ![385, 792633534417208834, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1101).pointIds 1101), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3353]
theorem treeEq3352 : B3352.tree = HexagonCover.NBand.M6900_7100.SplitData.node3352 := by
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
  · exact treeEq3353

def B3258 : Block := .branch 72 ![10384593717069655257060992658440577, 148366586124093621762, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B3259, B3352, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq3258 : B3258.tree = HexagonCover.NBand.M6900_7100.SplitData.node3258 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3259
  · exact treeEq3352
  · rfl
  · rfl
  · rfl

theorem accepted3258 : B3258.accepted = true := by decide +kernel
theorem checked3258 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3258 (maskNeeds ![10384593717069655257060992658440577, 148366586124093621762, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3258]
  exact B3258.sound accepted3258
#print axioms checked3258

def Tip3255_3258 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3258 ![10384593717069655257060992658440577, 148366586124093621762, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3258
def B3363 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 24584, 98320, 393248, 751211841609862171439950978327882504329706423713856] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 1140).pointIds 1140)]
theorem treeEq3363 : B3363.tree = HexagonCover.NBand.M6900_7100.SplitData.node3363 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3362 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648518346341352962, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1189).pointIds 1189), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3363]
theorem treeEq3362 : B3362.tree = HexagonCover.NBand.M6900_7100.SplitData.node3362 := by
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
  · exact treeEq3363

def B3361 : Block := .branch 171 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 377067422453151024379807970637523872642856417493056] ![B3362, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq3361 : B3361.tree = HexagonCover.NBand.M6900_7100.SplitData.node3361 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3362
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3360 : Block := .branch 151 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3361, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3360 : B3360.tree = HexagonCover.NBand.M6900_7100.SplitData.node3360 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3361
  · rfl

def B3359 : Block := .branch 170 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3360, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1102).pointIds 1102)]
theorem treeEq3359 : B3359.tree = HexagonCover.NBand.M6900_7100.SplitData.node3359 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3360
  · rfl
  · rfl

def B3358 : Block := .branch 161 ![385, 792633534417208834, 18446745173221185540, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), B3359]
theorem treeEq3358 : B3358.tree = HexagonCover.NBand.M6900_7100.SplitData.node3358 := by
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
  · exact treeEq3359

def B3257 : Block := .branch 71 ![10384593717069655257060992658440577, 148366586124093621762, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), Tip3255_3258, B3358, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq3257 : B3257.tree = HexagonCover.NBand.M6900_7100.SplitData.node3257 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3358
  · rfl
  · rfl
  · rfl

def B3369 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676637733623982043299532301799565491506872336, 393248, 1122433257491911512663687080580618449900027004846144] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 1116).pointIds 1116), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 1142).pointIds 1142)]
theorem treeEq3369 : B3369.tree = HexagonCover.NBand.M6900_7100.SplitData.node3369 := by
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

def B3368 : Block := .branch 133 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 1122433257491911512663687080580618449900027004846144] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), B3369, (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 1141).pointIds 1141)]
theorem treeEq3368 : B3368.tree = HexagonCover.NBand.M6900_7100.SplitData.node3368 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3369
  · rfl
  · rfl

def B3367 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648518346341352962, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1189).pointIds 1189), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3368]
theorem treeEq3367 : B3367.tree = HexagonCover.NBand.M6900_7100.SplitData.node3367 := by
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
  · exact treeEq3368

def B3366 : Block := .branch 171 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400446229881543836189542842432] ![B3367, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq3366 : B3366.tree = HexagonCover.NBand.M6900_7100.SplitData.node3366 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3367
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3365 : Block := .branch 151 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3366, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3365 : B3365.tree = HexagonCover.NBand.M6900_7100.SplitData.node3365 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3366
  · rfl

def B3364 : Block := .branch 170 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3365, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1106).pointIds 1106)]
theorem treeEq3364 : B3364.tree = HexagonCover.NBand.M6900_7100.SplitData.node3364 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3365
  · rfl
  · rfl

def B3256 : Block := .branch 68 ![10384593717069655257060992658440577, 148366586124093621762, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 445).pointIds 445), B3257, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B3364]
theorem treeEq3256 : B3256.tree = HexagonCover.NBand.M6900_7100.SplitData.node3256 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3257
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3364

def B3374 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080580470875947437328433216] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 1120).pointIds 1120)]
theorem treeEq3374 : B3374.tree = HexagonCover.NBand.M6900_7100.SplitData.node3374 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3373 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648518346341352962, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1189).pointIds 1189), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3374]
theorem treeEq3373 : B3373.tree = HexagonCover.NBand.M6900_7100.SplitData.node3373 := by
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
  · exact treeEq3374

def B3372 : Block := .branch 171 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400446229733969883599866429504] ![B3373, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1119).pointIds 1119)]
theorem treeEq3372 : B3372.tree = HexagonCover.NBand.M6900_7100.SplitData.node3372 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3373
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3371 : Block := .branch 151 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3372, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3371 : B3371.tree = HexagonCover.NBand.M6900_7100.SplitData.node3371 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3372
  · rfl

def B3370 : Block := .branch 170 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3371, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1118).pointIds 1118)]
theorem treeEq3370 : B3370.tree = HexagonCover.NBand.M6900_7100.SplitData.node3370 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3371
  · rfl
  · rfl

def B3255 : Block := .branch 67 ![10384593717069655257060992658440577, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 439).pointIds 439), B3256, (.leaf 2 (Common.fact 440).pointIds 440), (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), B3370]
theorem treeEq3255 : B3255.tree = HexagonCover.NBand.M6900_7100.SplitData.node3255 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3256
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3370

theorem accepted3255 : B3255.accepted = true := by decide +kernel
theorem checked3255 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3255 (maskNeeds ![10384593717069655257060992658440577, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3255]
  exact B3255.sound accepted3255
#print axioms checked3255

def B3397 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq3397 : B3397.tree = HexagonCover.NBand.M6900_7100.SplitData.node3397 := by
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
  · rfl

def B3396 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B3397, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1046).pointIds 1046)]
theorem treeEq3396 : B3396.tree = HexagonCover.NBand.M6900_7100.SplitData.node3396 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3397
  · rfl
  · rfl
  · rfl

def B3395 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B3396]
theorem treeEq3395 : B3395.tree = HexagonCover.NBand.M6900_7100.SplitData.node3395 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3396

def B3394 : Block := .branch 166 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B3395, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3394 : B3394.tree = HexagonCover.NBand.M6900_7100.SplitData.node3394 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3395
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3393 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B3394, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3393 : B3393.tree = HexagonCover.NBand.M6900_7100.SplitData.node3393 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3394
  · rfl

def B3406 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1058).pointIds 1058)]
theorem treeEq3406 : B3406.tree = HexagonCover.NBand.M6900_7100.SplitData.node3406 := by
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
  · rfl

def B3405 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B3406, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1057).pointIds 1057)]
theorem treeEq3405 : B3405.tree = HexagonCover.NBand.M6900_7100.SplitData.node3405 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3406
  · rfl
  · rfl
  · rfl

def B3404 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 186255823898127764478106319013159115297948532752, 393248, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B3405]
theorem treeEq3404 : B3404.tree = HexagonCover.NBand.M6900_7100.SplitData.node3404 := by
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
  · exact treeEq3405

def B3403 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B3404, (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3403 : B3403.tree = HexagonCover.NBand.M6900_7100.SplitData.node3403 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3404
  · rfl
  · rfl

def B3402 : Block := .branch 132 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 996).pointIds 996), (.leaf 5 (Common.fact 221).pointIds 221), B3403]
theorem treeEq3402 : B3402.tree = HexagonCover.NBand.M6900_7100.SplitData.node3402 := by
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
  · exact treeEq3403

def B3401 : Block := .branch 133 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 995).pointIds 995), (.leaf 5 (Common.fact 215).pointIds 215), B3402]
theorem treeEq3401 : B3401.tree = HexagonCover.NBand.M6900_7100.SplitData.node3401 := by
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
  · exact treeEq3402

def B3400 : Block := .branch 157 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B3401, (.leaf 5 (Common.fact 994).pointIds 994), (.leaf 0 [] 0)]
theorem treeEq3400 : B3400.tree = HexagonCover.NBand.M6900_7100.SplitData.node3400 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3401
  · rfl
  · rfl

def B3399 : Block := .branch 171 ![748288838313422304507415652620848621927823526855041, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B3400, (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq3399 : B3399.tree = HexagonCover.NBand.M6900_7100.SplitData.node3399 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3400
  · rfl

def B3398 : Block := .branch 169 ![10387129018270111715863986064851329, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B3399, (.leaf 1 (Common.fact 1192).pointIds 1192), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq3398 : B3398.tree = HexagonCover.NBand.M6900_7100.SplitData.node3398 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3399
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3392 : Block := .branch 108 ![10387129018270111715863986064851329, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B3393, (.leaf 5 (Common.fact 322).pointIds 322), B3398]
theorem treeEq3392 : B3392.tree = HexagonCover.NBand.M6900_7100.SplitData.node3392 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3393
  · rfl
  · exact treeEq3398

theorem accepted3392 : B3392.accepted = true := by decide +kernel
theorem checked3392 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3392 (maskNeeds ![10387129018270111715863986064851329, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3392]
  exact B3392.sound accepted3392
#print axioms checked3392

def Tip3390_3392 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3392 ![10387129018270111715863986064851329, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3392
def B3414 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq3414 : B3414.tree = HexagonCover.NBand.M6900_7100.SplitData.node3414 := by
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

def B3413 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B3414, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq3413 : B3413.tree = HexagonCover.NBand.M6900_7100.SplitData.node3413 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3414
  · rfl
  · rfl

def B3412 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B3413, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3412 : B3412.tree = HexagonCover.NBand.M6900_7100.SplitData.node3412 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3413
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3411 : Block := .branch 164 ![2993155353253689176481149013283026195015899646263681, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1060).pointIds 1060), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3412]
theorem treeEq3411 : B3411.tree = HexagonCover.NBand.M6900_7100.SplitData.node3411 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3412

def B3410 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 618970019642690137449563650, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1192).pointIds 1192), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3411]
theorem treeEq3410 : B3410.tree = HexagonCover.NBand.M6900_7100.SplitData.node3410 := by
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
  · exact treeEq3411

def B3409 : Block := .branch 171 ![2475880078570760549798248833, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B3410, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1059).pointIds 1059)]
theorem treeEq3409 : B3409.tree = HexagonCover.NBand.M6900_7100.SplitData.node3409 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3410
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3408 : Block := .branch 151 ![2475880078570760549798248833, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3409, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3408 : B3408.tree = HexagonCover.NBand.M6900_7100.SplitData.node3408 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3409
  · rfl

def B3407 : Block := .branch 170 ![2475880078570760549798248833, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3408, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq3407 : B3407.tree = HexagonCover.NBand.M6900_7100.SplitData.node3407 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3408
  · rfl
  · rfl

def B3391 : Block := .branch 101 ![10384596192949733827821542456689025, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip3390_3392, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B3407]
theorem treeEq3391 : B3391.tree = HexagonCover.NBand.M6900_7100.SplitData.node3391 := by
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
  · exact treeEq3407

def B3416 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1062).pointIds 1062)]
theorem treeEq3416 : B3416.tree = HexagonCover.NBand.M6900_7100.SplitData.node3416 := by
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
  · rfl

def B3415 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B3416, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1061).pointIds 1061)]
theorem treeEq3415 : B3415.tree = HexagonCover.NBand.M6900_7100.SplitData.node3415 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3416
  · rfl
  · rfl
  · rfl

def B3390 : Block := .branch 91 ![10384593717069655257060992658440577, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B3391, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B3415]
theorem treeEq3390 : B3390.tree = HexagonCover.NBand.M6900_7100.SplitData.node3390 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3391
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3415

theorem accepted3390 : B3390.accepted = true := by decide +kernel
theorem checked3390 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3390 (maskNeeds ![10384593717069655257060992658440577, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3390]
  exact B3390.sound accepted3390
#print axioms checked3390

def B3436 : Block := .branch 89 ![385, 748288838313422294120286634652968360967494755681794, 6148, 24584, 98320, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 1193).pointIds 1193), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), (.leaf 6 (Common.fact 1144).pointIds 1144)]
theorem treeEq3436 : B3436.tree = HexagonCover.NBand.M6900_7100.SplitData.node3436 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3435 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 928).pointIds 928), B3436, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3435 : B3435.tree = HexagonCover.NBand.M6900_7100.SplitData.node3435 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3436
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3434 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B3435]
theorem treeEq3434 : B3434.tree = HexagonCover.NBand.M6900_7100.SplitData.node3434 := by
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
  · exact treeEq3435

def B3433 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B3434, (.leaf 0 [] 0)]
theorem treeEq3433 : B3433.tree = HexagonCover.NBand.M6900_7100.SplitData.node3433 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3434
  · rfl

def B3432 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B3433, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3432 : B3432.tree = HexagonCover.NBand.M6900_7100.SplitData.node3432 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3433
  · rfl

def B3431 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B3432, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq3431 : B3431.tree = HexagonCover.NBand.M6900_7100.SplitData.node3431 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3432
  · rfl
  · rfl

def B3430 : Block := .branch 124 ![2993155353253689176481146537402947624255349848015233, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234659635666804290254306654289984] ![B3431, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 1072).pointIds 1072)]
theorem treeEq3430 : B3430.tree = HexagonCover.NBand.M6900_7100.SplitData.node3430 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3431
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3429 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3430]
theorem treeEq3429 : B3429.tree = HexagonCover.NBand.M6900_7100.SplitData.node3429 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3430

def B3428 : Block := .branch 171 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400678343343761939811733602368] ![B3429, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1071).pointIds 1071)]
theorem treeEq3428 : B3428.tree = HexagonCover.NBand.M6900_7100.SplitData.node3428 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3429
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3427 : Block := .branch 151 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3428, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3427 : B3427.tree = HexagonCover.NBand.M6900_7100.SplitData.node3427 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3428
  · rfl

def B3426 : Block := .branch 170 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3427, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq3426 : B3426.tree = HexagonCover.NBand.M6900_7100.SplitData.node3426 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3427
  · rfl
  · rfl

theorem accepted3426 : B3426.accepted = true := by decide +kernel
theorem checked3426 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3426 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896]) := by
  rw [← treeEq3426]
  exact B3426.sound accepted3426
#print axioms checked3426

end HexagonCover.NBand.M6900_7100.SplitTree.Run0045
