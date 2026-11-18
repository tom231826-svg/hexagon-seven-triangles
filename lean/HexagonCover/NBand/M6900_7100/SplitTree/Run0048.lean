import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0037
import HexagonCover.NBand.M6900_7100.SplitTree.Run0039
import HexagonCover.NBand.M6900_7100.SplitTree.Run0040
import HexagonCover.NBand.M6900_7100.SplitTree.Run0041
import HexagonCover.NBand.M6900_7100.SplitTree.Run0043
import HexagonCover.NBand.M6900_7100.SplitTree.Run0045
import HexagonCover.NBand.M6900_7100.SplitTree.Run0047
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0048
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2949_2959 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2959 ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0041.checked2959
def Tip2949_3084 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3084 ![10384593717069655257060992658440577, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0043.checked3084
def B2956 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 1123894759129242415581890765413039585014503584563264] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1176).pointIds 1176)]
theorem treeEq2956 : B2956.tree = HexagonCover.NBand.M6900_7100.SplitData.node2956 := by
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

def B2955 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1123894759129242415581890765413039585014503584563264] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2956, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 1175).pointIds 1175)]
theorem treeEq2955 : B2955.tree = HexagonCover.NBand.M6900_7100.SplitData.node2955 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2956
  · rfl
  · rfl

def B2954 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 612489549322388994, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 375605920815820121461604131062302678950666122559552] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1173).pointIds 1173), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2955]
theorem treeEq2954 : B2954.tree = HexagonCover.NBand.M6900_7100.SplitData.node2954 := by
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
  · exact treeEq2955

def B2953 : Block := .branch 171 ![385, 756604737398244866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 375605920815820121461604131062302678950666122559552] ![B2954, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1172).pointIds 1172)]
theorem treeEq2953 : B2953.tree = HexagonCover.NBand.M6900_7100.SplitData.node2953 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2954
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2952 : Block := .branch 151 ![385, 756604737398244866, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 375605920815820121461604440547312500295734847340608] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2953, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2952 : B2952.tree = HexagonCover.NBand.M6900_7100.SplitData.node2952 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2953
  · rfl

def B2951 : Block := .branch 170 ![385, 756604737398244866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 375605920815820121461604440547312500295734847340608] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B2952, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1169).pointIds 1169)]
theorem treeEq2951 : B2951.tree = HexagonCover.NBand.M6900_7100.SplitData.node2951 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2952
  · rfl
  · rfl

def B2950 : Block := .branch 160 ![385, 756604737398244866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1165).pointIds 1165), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2951]
theorem treeEq2950 : B2950.tree = HexagonCover.NBand.M6900_7100.SplitData.node2950 := by
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
  · exact treeEq2951

def B3082 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648659083829708290, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1180).pointIds 1180), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq3082 : B3082.tree = HexagonCover.NBand.M6900_7100.SplitData.node3082 := by
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

def B3081 : Block := .branch 171 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974311749925714704515727424] ![B3082, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq3081 : B3081.tree = HexagonCover.NBand.M6900_7100.SplitData.node3081 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3082
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3080 : Block := .branch 151 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3081, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3080 : B3080.tree = HexagonCover.NBand.M6900_7100.SplitData.node3080 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3081
  · rfl

def B3079 : Block := .branch 170 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3080, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq3079 : B3079.tree = HexagonCover.NBand.M6900_7100.SplitData.node3079 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3080
  · rfl
  · rfl

def B2958 : Block := .branch 65 ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), Tip2949_2959, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B3079]
theorem treeEq2958 : B2958.tree = HexagonCover.NBand.M6900_7100.SplitData.node2958 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3079

def B3252 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906204574950360578, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1188).pointIds 1188), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1124).pointIds 1124)]
theorem treeEq3252 : B3252.tree = HexagonCover.NBand.M6900_7100.SplitData.node3252 := by
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
  · rfl

def B3251 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 928).pointIds 928), B3252, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq3251 : B3251.tree = HexagonCover.NBand.M6900_7100.SplitData.node3251 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3252
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3250 : Block := .branch 171 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974311749925714704515727424] ![B3251, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq3250 : B3250.tree = HexagonCover.NBand.M6900_7100.SplitData.node3250 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3251
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3249 : Block := .branch 151 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3250, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3249 : B3249.tree = HexagonCover.NBand.M6900_7100.SplitData.node3249 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3250
  · rfl

def B3248 : Block := .branch 170 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3249, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq3248 : B3248.tree = HexagonCover.NBand.M6900_7100.SplitData.node3248 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3249
  · rfl
  · rfl

def B3083 : Block := .branch 65 ![10384593717069655257060992658440577, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), Tip2949_3084, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B3248]
theorem treeEq3083 : B3083.tree = HexagonCover.NBand.M6900_7100.SplitData.node3083 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3248

def B2957 : Block := .branch 56 ![10384593717069655257060992658440577, 720716677867636226, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 165).pointIds 165), B2958, B3083, (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), (.leaf 6 (Common.fact 169).pointIds 169)]
theorem treeEq2957 : B2957.tree = HexagonCover.NBand.M6900_7100.SplitData.node2957 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2958
  · exact treeEq3083
  · rfl
  · rfl
  · rfl
  · rfl

def B2949 : Block := .branch 55 ![10384593717069655257060992658440577, 720716677867636226, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 99).pointIds 99), B2950, B2957, (.leaf 3 (Common.fact 100).pointIds 100), (.leaf 4 (Common.fact 101).pointIds 101), (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 103).pointIds 103)]
theorem treeEq2949 : B2949.tree = HexagonCover.NBand.M6900_7100.SplitData.node2949 := by
  change Tree.branch (55 : Fin 173) _ = Tree.branch (55 : Fin 173) _
  apply congrArg (Tree.branch (55 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2950
  · exact treeEq2957
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2949 : B2949.accepted = true := by decide +kernel
theorem checked2949 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2949 (maskNeeds ![10384593717069655257060992658440577, 720716677867636226, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2949]
  exact B2949.sound accepted2949
#print axioms checked2949

def Tip0016_2632 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2632 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0037.checked2632
def Tip0016_2756 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2756 ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0039.checked2756
def Tip0016_0017 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0017 ![385, 144257025075840514, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0040.checked0017
def B2755 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq2755 : B2755.tree = HexagonCover.NBand.M6900_7100.SplitData.node2755 := by
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

def B2754 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974311749925714704515727424] ![B2755, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq2754 : B2754.tree = HexagonCover.NBand.M6900_7100.SplitData.node2754 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2755
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2753 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2754, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2753 : B2753.tree = HexagonCover.NBand.M6900_7100.SplitData.node2753 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2754
  · rfl

def B2752 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2753, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq2752 : B2752.tree = HexagonCover.NBand.M6900_7100.SplitData.node2752 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2753
  · rfl
  · rfl

def B2631 : Block := .branch 65 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), Tip0016_2632, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B2752]
theorem treeEq2631 : B2631.tree = HexagonCover.NBand.M6900_7100.SplitData.node2631 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2752

def B2630 : Block := .branch 56 ![10384593717069655257060992658440577, 720577039890908674, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 165).pointIds 165), B2631, Tip0016_2756, (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), (.leaf 6 (Common.fact 169).pointIds 169)]
theorem treeEq2630 : B2630.tree = HexagonCover.NBand.M6900_7100.SplitData.node2630 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2631
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2629 : Block := .branch 59 ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 390).pointIds 390), B2630, (.leaf 2 (Common.fact 378).pointIds 378), (.leaf 3 (Common.fact 379).pointIds 379), (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq2629 : B2629.tree = HexagonCover.NBand.M6900_7100.SplitData.node2629 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2630
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2628 : Block := .branch 113 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B2629, (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq2628 : B2628.tree = HexagonCover.NBand.M6900_7100.SplitData.node2628 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2629
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2627 : Block := .branch 168 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 1125).pointIds 1125), (.leaf 2 (Common.fact 1126).pointIds 1126), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2628]
theorem treeEq2627 : B2627.tree = HexagonCover.NBand.M6900_7100.SplitData.node2627 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2628

def B0016 : Block := .branch 47 ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), Tip0016_0017, B2627, (.leaf 3 (Common.fact 95).pointIds 95), (.leaf 4 (Common.fact 96).pointIds 96), (.leaf 5 (Common.fact 97).pointIds 97), (.leaf 6 (Common.fact 98).pointIds 98)]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M6900_7100.SplitData.node0016 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2627
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0016 : B0016.accepted = true := by decide +kernel
theorem checked0016 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0016 (maskNeeds ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0016]
  exact B0016.sound accepted0016
#print axioms checked0016

def Tip0006_3255 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3255 ![10384593717069655257060992658440577, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0045.checked3255
def Tip0006_3379 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3379 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0047.checked3379
def Tip0006_2949 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2949 ![10384593717069655257060992658440577, 720716677867636226, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2949
def Tip0006_0016 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0016 ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0016
def B3378 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648518346341352962, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1189).pointIds 1189), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq3378 : B3378.tree = HexagonCover.NBand.M6900_7100.SplitData.node3378 := by
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

def B3377 : Block := .branch 171 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974311749925714704515727424] ![B3378, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq3377 : B3377.tree = HexagonCover.NBand.M6900_7100.SplitData.node3377 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3378
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3376 : Block := .branch 151 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3377, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3376 : B3376.tree = HexagonCover.NBand.M6900_7100.SplitData.node3376 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3377
  · rfl

def B3375 : Block := .branch 170 ![385, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3376, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq3375 : B3375.tree = HexagonCover.NBand.M6900_7100.SplitData.node3375 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3376
  · rfl
  · rfl

def B3254 : Block := .branch 65 ![10384593717069655257060992658440577, 792633534417208834, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), Tip0006_3255, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B3375]
theorem treeEq3254 : B3254.tree = HexagonCover.NBand.M6900_7100.SplitData.node3254 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3375

def B3253 : Block := .branch 56 ![10384593717069655257060992658440577, 720575940379280898, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 165).pointIds 165), B3254, Tip0006_3379, (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), (.leaf 6 (Common.fact 169).pointIds 169)]
theorem treeEq3253 : B3253.tree = HexagonCover.NBand.M6900_7100.SplitData.node3253 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3254
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2948 : Block := .branch 47 ![10384593717069655257060992658440577, 720575940379280898, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 94).pointIds 94), Tip0006_2949, B3253, (.leaf 3 (Common.fact 95).pointIds 95), (.leaf 4 (Common.fact 96).pointIds 96), (.leaf 5 (Common.fact 97).pointIds 97), (.leaf 6 (Common.fact 98).pointIds 98)]
theorem treeEq2948 : B2948.tree = HexagonCover.NBand.M6900_7100.SplitData.node2948 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3253
  · rfl
  · rfl
  · rfl
  · rfl

def B2947 : Block := .branch 59 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 390).pointIds 390), B2948, (.leaf 2 (Common.fact 378).pointIds 378), (.leaf 3 (Common.fact 379).pointIds 379), (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq2947 : B2947.tree = HexagonCover.NBand.M6900_7100.SplitData.node2947 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2948
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2946 : Block := .branch 113 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B2947, (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 256).pointIds 256), (.leaf 5 (Common.fact 257).pointIds 257), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq2946 : B2946.tree = HexagonCover.NBand.M6900_7100.SplitData.node2946 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2947
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2945 : Block := .branch 168 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 391).pointIds 391), (.leaf 1 (Common.fact 1163).pointIds 1163), (.leaf 2 (Common.fact 1164).pointIds 1164), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2946]
theorem treeEq2945 : B2945.tree = HexagonCover.NBand.M6900_7100.SplitData.node2945 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2946

def B0015 : Block := .branch 40 ![385, 144115188075857410, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 90).pointIds 90), Tip0006_0016, B2945, (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), (.leaf 0 [] 0)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M6900_7100.SplitData.node0015 := by
  change Tree.branch (40 : Fin 173) _ = Tree.branch (40 : Fin 173) _
  apply congrArg (Tree.branch (40 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2945
  · rfl
  · rfl
  · rfl
  · rfl

def B0014 : Block := .branch 57 ![385, 1538, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 84).pointIds 84), B0015, (.leaf 2 (Common.fact 85).pointIds 85), (.leaf 3 (Common.fact 86).pointIds 86), (.leaf 4 (Common.fact 87).pointIds 87), (.leaf 5 (Common.fact 88).pointIds 88), (.leaf 6 (Common.fact 89).pointIds 89)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M6900_7100.SplitData.node0014 := by
  change Tree.branch (57 : Fin 173) _ = Tree.branch (57 : Fin 173) _
  apply congrArg (Tree.branch (57 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0015
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0013 : Block := .branch 64 ![385, 1538, 6148, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 78).pointIds 78), (.leaf 1 (Common.fact 79).pointIds 79), B0014, (.leaf 3 (Common.fact 80).pointIds 80), (.leaf 4 (Common.fact 81).pointIds 81), (.leaf 5 (Common.fact 82).pointIds 82), (.leaf 6 (Common.fact 83).pointIds 83)]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M6900_7100.SplitData.node0013 := by
  change Tree.branch (64 : Fin 173) _ = Tree.branch (64 : Fin 173) _
  apply congrArg (Tree.branch (64 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0014
  · rfl
  · rfl
  · rfl
  · rfl

def B0012 : Block := .branch 149 ![385, 1538, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 72).pointIds 72), (.leaf 1 (Common.fact 73).pointIds 73), (.leaf 2 (Common.fact 74).pointIds 74), (.leaf 3 (Common.fact 75).pointIds 75), B0013, (.leaf 5 (Common.fact 76).pointIds 76), (.leaf 6 (Common.fact 77).pointIds 77)]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M6900_7100.SplitData.node0012 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0013
  · rfl
  · rfl

def B0011 : Block := .branch 98 ![385, 1538, 6148, 79266848140492005727134572552, 98320, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 66).pointIds 66), (.leaf 1 (Common.fact 67).pointIds 67), (.leaf 2 (Common.fact 68).pointIds 68), (.leaf 3 (Common.fact 69).pointIds 69), (.leaf 4 (Common.fact 70).pointIds 70), (.leaf 5 (Common.fact 71).pointIds 71), B0012]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M6900_7100.SplitData.node0011 := by
  change Tree.branch (98 : Fin 173) _ = Tree.branch (98 : Fin 173) _
  apply congrArg (Tree.branch (98 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0012

def B0010 : Block := .branch 85 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 60).pointIds 60), (.leaf 1 (Common.fact 61).pointIds 61), (.leaf 2 (Common.fact 62).pointIds 62), B0011, (.leaf 4 (Common.fact 63).pointIds 63), (.leaf 5 (Common.fact 64).pointIds 64), (.leaf 6 (Common.fact 65).pointIds 65)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M6900_7100.SplitData.node0010 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 48 ![385, 1538, 9223372036854781956, 79228162514264337593543974920, 98320, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 54).pointIds 54), B0010, (.leaf 2 (Common.fact 55).pointIds 55), (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M6900_7100.SplitData.node0009 := by
  change Tree.branch (48 : Fin 173) _ = Tree.branch (48 : Fin 173) _
  apply congrArg (Tree.branch (48 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 63 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 48).pointIds 48), (.leaf 1 (Common.fact 49).pointIds 49), B0009, (.leaf 3 (Common.fact 50).pointIds 50), (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M6900_7100.SplitData.node0008 := by
  change Tree.branch (63 : Fin 173) _ = Tree.branch (63 : Fin 173) _
  apply congrArg (Tree.branch (63 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 96 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 42).pointIds 42), (.leaf 1 (Common.fact 43).pointIds 43), (.leaf 2 (Common.fact 44).pointIds 44), B0008, (.leaf 4 (Common.fact 45).pointIds 45), (.leaf 5 (Common.fact 46).pointIds 46), (.leaf 6 (Common.fact 47).pointIds 47)]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M6900_7100.SplitData.node0007 := by
  change Tree.branch (96 : Fin 173) _ = Tree.branch (96 : Fin 173) _
  apply congrArg (Tree.branch (96 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0008
  · rfl
  · rfl
  · rfl

def B0006 : Block := .branch 105 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 36).pointIds 36), (.leaf 1 (Common.fact 37).pointIds 37), (.leaf 2 (Common.fact 38).pointIds 38), B0007, (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M6900_7100.SplitData.node0006 := by
  change Tree.branch (105 : Fin 173) _ = Tree.branch (105 : Fin 173) _
  apply congrArg (Tree.branch (105 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0007
  · rfl
  · rfl
  · rfl

theorem accepted0006 : B0006.accepted = true := by decide +kernel
theorem checked0006 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0006 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940525889170706893786007994432]) := by
  rw [← treeEq0006]
  exact B0006.sound accepted0006
#print axioms checked0006

def Tip0000_0006 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0006 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940525889170706893786007994432] checked0006
def B0005 : Block := .branch 148 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), (.leaf 2 (Common.fact 32).pointIds 32), (.leaf 3 (Common.fact 33).pointIds 33), Tip0000_0006, (.leaf 5 (Common.fact 34).pointIds 34), (.leaf 6 (Common.fact 35).pointIds 35)]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M6900_7100.SplitData.node0005 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0004 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 464227514732018152842461248] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), (.leaf 2 (Common.fact 26).pointIds 26), (.leaf 3 (Common.fact 27).pointIds 27), (.leaf 4 (Common.fact 28).pointIds 28), (.leaf 5 (Common.fact 29).pointIds 29), B0005]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M6900_7100.SplitData.node0004 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0005

def B0003 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 464227514732018152842461248] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), (.leaf 2 (Common.fact 20).pointIds 20), (.leaf 3 (Common.fact 21).pointIds 21), (.leaf 4 (Common.fact 22).pointIds 22), (.leaf 5 (Common.fact 23).pointIds 23), B0004]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M6900_7100.SplitData.node0003 := by
  change Tree.branch (110 : Fin 173) _ = Tree.branch (110 : Fin 173) _
  apply congrArg (Tree.branch (110 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0004

def B0002 : Block := .branch 99 ![385, 1538, 6148, 24584, 98320, 393248, 464227514732018152842461248] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), (.leaf 3 (Common.fact 15).pointIds 15), (.leaf 4 (Common.fact 16).pointIds 16), (.leaf 5 (Common.fact 17).pointIds 17), B0003]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M6900_7100.SplitData.node0002 := by
  change Tree.branch (99 : Fin 173) _ = Tree.branch (99 : Fin 173) _
  apply congrArg (Tree.branch (99 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0003

def B0001 : Block := .branch 88 ![385, 1538, 6148, 24584, 98320, 393248, 154742504910673084117680192] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), (.leaf 2 (Common.fact 8).pointIds 8), (.leaf 3 (Common.fact 9).pointIds 9), (.leaf 4 (Common.fact 10).pointIds 10), (.leaf 5 (Common.fact 11).pointIds 11), B0002]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M6900_7100.SplitData.node0001 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0002

def B0000 : Block := .branch 87 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M6900_7100.SplitData.node0000 := by
  change Tree.branch (87 : Fin 173) _ = Tree.branch (87 : Fin 173) _
  apply congrArg (Tree.branch (87 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0001

theorem accepted0000 : B0000.accepted = true := by decide +kernel
theorem checked0000 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M6900_7100.SplitTree.Run0048
