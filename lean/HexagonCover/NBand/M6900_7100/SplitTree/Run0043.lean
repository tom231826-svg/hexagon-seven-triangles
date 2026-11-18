import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0042
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0043
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B3219 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906204574950360578, 6148, 24584, 98320, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1188).pointIds 1188), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1099).pointIds 1099)]
theorem treeEq3219 : B3219.tree = HexagonCover.NBand.M6900_7100.SplitData.node3219 := by
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

def B3218 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B3219, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq3218 : B3218.tree = HexagonCover.NBand.M6900_7100.SplitData.node3218 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3219
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3217 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B3218]
theorem treeEq3217 : B3217.tree = HexagonCover.NBand.M6900_7100.SplitData.node3217 := by
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
  · exact treeEq3218

def B3216 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B3217, (.leaf 0 [] 0)]
theorem treeEq3216 : B3216.tree = HexagonCover.NBand.M6900_7100.SplitData.node3216 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3217
  · rfl

def B3215 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B3216, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3215 : B3215.tree = HexagonCover.NBand.M6900_7100.SplitData.node3215 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3216
  · rfl

def B3214 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B3215, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq3214 : B3214.tree = HexagonCover.NBand.M6900_7100.SplitData.node3214 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3215
  · rfl
  · rfl

def B3213 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3214, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq3213 : B3213.tree = HexagonCover.NBand.M6900_7100.SplitData.node3213 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3214
  · rfl

def B3212 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3213, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3212 : B3212.tree = HexagonCover.NBand.M6900_7100.SplitData.node3212 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3213
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3211 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3212]
theorem treeEq3211 : B3211.tree = HexagonCover.NBand.M6900_7100.SplitData.node3211 := by
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
  · exact treeEq3212

def B3210 : Block := .branch 171 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3211, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq3210 : B3210.tree = HexagonCover.NBand.M6900_7100.SplitData.node3210 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3211
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3209 : Block := .branch 151 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3210, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3209 : B3209.tree = HexagonCover.NBand.M6900_7100.SplitData.node3209 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3210
  · rfl

def B3208 : Block := .branch 170 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3209, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq3208 : B3208.tree = HexagonCover.NBand.M6900_7100.SplitData.node3208 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3209
  · rfl
  · rfl

def B3207 : Block := .branch 172 ![385, 144255925564212738, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1101).pointIds 1101), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3208]
theorem treeEq3207 : B3207.tree = HexagonCover.NBand.M6900_7100.SplitData.node3207 := by
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
  · exact treeEq3208

theorem accepted3207 : B3207.accepted = true := by decide +kernel
theorem checked3207 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3207 (maskNeeds ![385, 144255925564212738, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3207]
  exact B3207.sound accepted3207
#print axioms checked3207

def Tip3087_3154 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3154 ![10384593717070245552871351364092289, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0042.checked3154
def Tip3087_3091 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3091 ![10384593717069655257060992658440577, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0042.checked3091
def Tip3087_3181 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3181 ![385, 144255925564212738, 18446745173221185540, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0042.checked3181
def Tip3087_3194 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3194 ![385, 144255925564212738, 18446745173221185540, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0042.checked3194
def Tip3087_3207 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3207 ![385, 144255925564212738, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3207
def B3180 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq3180 : B3180.tree = HexagonCover.NBand.M6900_7100.SplitData.node3180 := by
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

def B3179 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B3180, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq3179 : B3179.tree = HexagonCover.NBand.M6900_7100.SplitData.node3179 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3180
  · rfl
  · rfl

def B3178 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 737869903685870421506, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1187).pointIds 1187), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3179]
theorem treeEq3178 : B3178.tree = HexagonCover.NBand.M6900_7100.SplitData.node3178 := by
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
  · exact treeEq3179

def B3177 : Block := .branch 171 ![2475880078570760549798248833, 738014018873946277378, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 1461501659108974401460659219987178972127352586304] ![B3178, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq3177 : B3177.tree = HexagonCover.NBand.M6900_7100.SplitData.node3177 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3178
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3176 : Block := .branch 151 ![2475880078570760549798248833, 738014018873946277378, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3177, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3176 : B3176.tree = HexagonCover.NBand.M6900_7100.SplitData.node3176 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3177
  · rfl

def B3175 : Block := .branch 170 ![2475880078570760549798248833, 738014018873946277378, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3176, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1089).pointIds 1089)]
theorem treeEq3175 : B3175.tree = HexagonCover.NBand.M6900_7100.SplitData.node3175 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3176
  · rfl
  · rfl

def B3174 : Block := .branch 160 ![2475880078570760549798248833, 738014018873946277378, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1186).pointIds 1186), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B3175]
theorem treeEq3174 : B3174.tree = HexagonCover.NBand.M6900_7100.SplitData.node3174 := by
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
  · exact treeEq3175

def B3153 : Block := .branch 69 ![10384596192949733827821542456689025, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip3087_3154, B3174, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq3153 : B3153.tree = HexagonCover.NBand.M6900_7100.SplitData.node3153 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3174
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3152 : Block := .branch 91 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B3153, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq3152 : B3152.tree = HexagonCover.NBand.M6900_7100.SplitData.node3152 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3153
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3090 : Block := .branch 76 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip3087_3091, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B3152]
theorem treeEq3090 : B3090.tree = HexagonCover.NBand.M6900_7100.SplitData.node3090 := by
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
  · exact treeEq3152

def B3089 : Block := .branch 74 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B3090, Tip3087_3181, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq3089 : B3089.tree = HexagonCover.NBand.M6900_7100.SplitData.node3089 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3090
  · rfl
  · rfl
  · rfl
  · rfl

def B3088 : Block := .branch 73 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B3089, Tip3087_3194, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq3088 : B3088.tree = HexagonCover.NBand.M6900_7100.SplitData.node3088 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3089
  · rfl
  · rfl
  · rfl
  · rfl

def B3087 : Block := .branch 72 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B3088, Tip3087_3207, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq3087 : B3087.tree = HexagonCover.NBand.M6900_7100.SplitData.node3087 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3088
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3087 : B3087.accepted = true := by decide +kernel
theorem checked3087 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3087 (maskNeeds ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3087]
  exact B3087.sound accepted3087
#print axioms checked3087

def B3241 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676637733623982043299532301799565491506872336, 393248, 7132127990196584312316922045317412258702313083371584] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 1116).pointIds 1116), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 1117).pointIds 1117)]
theorem treeEq3241 : B3241.tree = HexagonCover.NBand.M6900_7100.SplitData.node3241 := by
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

def B3240 : Block := .branch 133 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 7132127990196584312316922045317412258702313083371584] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), B3241, (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 1115).pointIds 1115)]
theorem treeEq3240 : B3240.tree = HexagonCover.NBand.M6900_7100.SplitData.node3240 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3241
  · rfl
  · rfl

def B3239 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 737869903685870421506, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196635410966675352638475621367872] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1187).pointIds 1187), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3240]
theorem treeEq3239 : B3239.tree = HexagonCover.NBand.M6900_7100.SplitData.node3239 := by
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
  · exact treeEq3240

def B3238 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 147574093327164769794, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952478359237320661384159559744] ![(.leaf 0 (Common.fact 1073).pointIds 1073), B3239, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1114).pointIds 1114)]
theorem treeEq3238 : B3238.tree = HexagonCover.NBand.M6900_7100.SplitData.node3238 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3239
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3237 : Block := .branch 71 ![2993155353253689176481146537402947624255349848015233, 147574093327164769794, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952478359237320661384159559744] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), B3238, (.leaf 3 (Common.fact 1113).pointIds 1113), (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq3237 : B3237.tree = HexagonCover.NBand.M6900_7100.SplitData.node3237 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3238
  · rfl
  · rfl
  · rfl
  · rfl

def B3236 : Block := .branch 72 ![2993155353253689176481146537402947624255349848015233, 147574093327164769794, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B3237, (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq3236 : B3236.tree = HexagonCover.NBand.M6900_7100.SplitData.node3236 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3237
  · rfl
  · rfl
  · rfl
  · rfl

def B3235 : Block := .branch 73 ![2993155353253689176481146537402947624255349848015233, 147574093327164769794, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B3236, (.leaf 3 (Common.fact 1111).pointIds 1111), (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq3235 : B3235.tree = HexagonCover.NBand.M6900_7100.SplitData.node3235 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3236
  · rfl
  · rfl
  · rfl
  · rfl

def B3234 : Block := .branch 74 ![2993155353253689176481146537402947624255349848015233, 147574093327164769794, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B3235, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq3234 : B3234.tree = HexagonCover.NBand.M6900_7100.SplitData.node3234 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3235
  · rfl
  · rfl
  · rfl
  · rfl

def B3233 : Block := .branch 75 ![2993155353253689176481146537402947624255349848015233, 147574093327164769794, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 6383839151883162018196952787844247142006452884340800] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), B3234, (.leaf 3 (Common.fact 1109).pointIds 1109), (.leaf 4 (Common.fact 988).pointIds 988), (.leaf 5 (Common.fact 989).pointIds 989), (.leaf 6 (Common.fact 1110).pointIds 1110)]
theorem treeEq3233 : B3233.tree = HexagonCover.NBand.M6900_7100.SplitData.node3233 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3234
  · rfl
  · rfl
  · rfl
  · rfl

def B3232 : Block := .branch 172 ![2993155353253689176481146537402947624255349848015233, 147718208515240625666, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3233]
theorem treeEq3232 : B3232.tree = HexagonCover.NBand.M6900_7100.SplitData.node3232 := by
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
  · exact treeEq3233

def B3231 : Block := .branch 161 ![2993155353253689176481146537402947624255349848015233, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), B3232, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1108).pointIds 1108)]
theorem treeEq3231 : B3231.tree = HexagonCover.NBand.M6900_7100.SplitData.node3231 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3232
  · rfl
  · rfl
  · rfl

def B3230 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3231]
theorem treeEq3230 : B3230.tree = HexagonCover.NBand.M6900_7100.SplitData.node3230 := by
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
  · exact treeEq3231

def B3229 : Block := .branch 171 ![385, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![B3230, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq3229 : B3229.tree = HexagonCover.NBand.M6900_7100.SplitData.node3229 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3230
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3228 : Block := .branch 151 ![385, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3229, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3228 : B3228.tree = HexagonCover.NBand.M6900_7100.SplitData.node3228 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3229
  · rfl

def B3227 : Block := .branch 170 ![385, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3228, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1106).pointIds 1106)]
theorem treeEq3227 : B3227.tree = HexagonCover.NBand.M6900_7100.SplitData.node3227 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3228
  · rfl
  · rfl

theorem accepted3227 : B3227.accepted = true := by decide +kernel
theorem checked3227 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3227 (maskNeeds ![385, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488]) := by
  rw [← treeEq3227]
  exact B3227.sound accepted3227
#print axioms checked3227

def Tip3084_3087 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3087 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3087
def Tip3084_3227 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3227 ![385, 147718208515240625666, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] checked3227
def B3226 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906204574950360578, 6148, 24584, 98320, 393248, 377067422453151024379807970637523872642856417493056] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1188).pointIds 1188), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq3226 : B3226.tree = HexagonCover.NBand.M6900_7100.SplitData.node3226 := by
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

def B3225 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 400451448650445471071066927960984400957351338180672] ![(.leaf 0 (Common.fact 928).pointIds 928), B3226, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1104).pointIds 1104)]
theorem treeEq3225 : B3225.tree = HexagonCover.NBand.M6900_7100.SplitData.node3225 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3226
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3224 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379807970637523872642856417493056] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3225]
theorem treeEq3224 : B3224.tree = HexagonCover.NBand.M6900_7100.SplitData.node3224 := by
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
  · exact treeEq3225

def B3223 : Block := .branch 171 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 377067422453151024379807970637523872642856417493056] ![B3224, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq3223 : B3223.tree = HexagonCover.NBand.M6900_7100.SplitData.node3223 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3224
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3222 : Block := .branch 151 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3223, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3222 : B3222.tree = HexagonCover.NBand.M6900_7100.SplitData.node3222 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3223
  · rfl

def B3221 : Block := .branch 170 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3222, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1102).pointIds 1102)]
theorem treeEq3221 : B3221.tree = HexagonCover.NBand.M6900_7100.SplitData.node3221 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3222
  · rfl
  · rfl

def B3220 : Block := .branch 161 ![385, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), B3221]
theorem treeEq3220 : B3220.tree = HexagonCover.NBand.M6900_7100.SplitData.node3220 := by
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
  · exact treeEq3221

def B3086 : Block := .branch 71 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), Tip3084_3087, B3220, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq3086 : B3086.tree = HexagonCover.NBand.M6900_7100.SplitData.node3086 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3220
  · rfl
  · rfl
  · rfl

def B3085 : Block := .branch 68 ![10384593717069655257060992658440577, 147718208515240625666, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 445).pointIds 445), B3086, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), Tip3084_3227]
theorem treeEq3085 : B3085.tree = HexagonCover.NBand.M6900_7100.SplitData.node3085 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3086
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3247 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906204574950360578, 6148, 24584, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1188).pointIds 1188), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1121).pointIds 1121)]
theorem treeEq3247 : B3247.tree = HexagonCover.NBand.M6900_7100.SplitData.node3247 := by
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

def B3246 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 397528445375783665234659403553194498198094787117120] ![(.leaf 0 (Common.fact 928).pointIds 928), B3247, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1120).pointIds 1120)]
theorem treeEq3246 : B3246.tree = HexagonCover.NBand.M6900_7100.SplitData.node3246 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3247
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3245 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 140737488356866, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3246]
theorem treeEq3245 : B3245.tree = HexagonCover.NBand.M6900_7100.SplitData.node3245 := by
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
  · exact treeEq3246

def B3244 : Block := .branch 171 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400446229733969883599866429504] ![B3245, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1119).pointIds 1119)]
theorem treeEq3244 : B3244.tree = HexagonCover.NBand.M6900_7100.SplitData.node3244 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3245
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3243 : Block := .branch 151 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3244, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3243 : B3243.tree = HexagonCover.NBand.M6900_7100.SplitData.node3243 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3244
  · rfl

def B3242 : Block := .branch 170 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3243, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1118).pointIds 1118)]
theorem treeEq3242 : B3242.tree = HexagonCover.NBand.M6900_7100.SplitData.node3242 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3243
  · rfl
  · rfl

def B3084 : Block := .branch 67 ![10384593717069655257060992658440577, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 439).pointIds 439), B3085, (.leaf 2 (Common.fact 440).pointIds 440), (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), B3242]
theorem treeEq3084 : B3084.tree = HexagonCover.NBand.M6900_7100.SplitData.node3084 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3085
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3242

theorem accepted3084 : B3084.accepted = true := by decide +kernel
theorem checked3084 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3084 (maskNeeds ![10384593717069655257060992658440577, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3084]
  exact B3084.sound accepted3084
#print axioms checked3084

def B3272 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq3272 : B3272.tree = HexagonCover.NBand.M6900_7100.SplitData.node3272 := by
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

def B3271 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B3272, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1046).pointIds 1046)]
theorem treeEq3271 : B3271.tree = HexagonCover.NBand.M6900_7100.SplitData.node3271 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3272
  · rfl
  · rfl
  · rfl

def B3270 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B3271]
theorem treeEq3270 : B3270.tree = HexagonCover.NBand.M6900_7100.SplitData.node3270 := by
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
  · exact treeEq3271

def B3269 : Block := .branch 166 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B3270, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3269 : B3269.tree = HexagonCover.NBand.M6900_7100.SplitData.node3269 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3270
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3268 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B3269, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3268 : B3268.tree = HexagonCover.NBand.M6900_7100.SplitData.node3268 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3269
  · rfl

def B3281 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1058).pointIds 1058)]
theorem treeEq3281 : B3281.tree = HexagonCover.NBand.M6900_7100.SplitData.node3281 := by
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

def B3280 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B3281, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1057).pointIds 1057)]
theorem treeEq3280 : B3280.tree = HexagonCover.NBand.M6900_7100.SplitData.node3280 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3281
  · rfl
  · rfl
  · rfl

def B3279 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 186255823898127764478106319013159115297948532752, 393248, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B3280]
theorem treeEq3279 : B3279.tree = HexagonCover.NBand.M6900_7100.SplitData.node3279 := by
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
  · exact treeEq3280

def B3278 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B3279, (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3278 : B3278.tree = HexagonCover.NBand.M6900_7100.SplitData.node3278 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3279
  · rfl
  · rfl

def B3277 : Block := .branch 132 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 996).pointIds 996), (.leaf 5 (Common.fact 221).pointIds 221), B3278]
theorem treeEq3277 : B3277.tree = HexagonCover.NBand.M6900_7100.SplitData.node3277 := by
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
  · exact treeEq3278

def B3276 : Block := .branch 133 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 995).pointIds 995), (.leaf 5 (Common.fact 215).pointIds 215), B3277]
theorem treeEq3276 : B3276.tree = HexagonCover.NBand.M6900_7100.SplitData.node3276 := by
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
  · exact treeEq3277

def B3275 : Block := .branch 157 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B3276, (.leaf 5 (Common.fact 994).pointIds 994), (.leaf 0 [] 0)]
theorem treeEq3275 : B3275.tree = HexagonCover.NBand.M6900_7100.SplitData.node3275 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3276
  · rfl
  · rfl

def B3274 : Block := .branch 171 ![748288838313422304507415652620848621927823526855041, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B3275, (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq3274 : B3274.tree = HexagonCover.NBand.M6900_7100.SplitData.node3274 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3275
  · rfl

def B3273 : Block := .branch 169 ![10387129018270111715863986064851329, 792633534417208834, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B3274, (.leaf 1 (Common.fact 1189).pointIds 1189), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq3273 : B3273.tree = HexagonCover.NBand.M6900_7100.SplitData.node3273 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3274
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3267 : Block := .branch 108 ![10387129018270111715863986064851329, 792633534417208834, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B3268, (.leaf 5 (Common.fact 322).pointIds 322), B3273]
theorem treeEq3267 : B3267.tree = HexagonCover.NBand.M6900_7100.SplitData.node3267 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3268
  · rfl
  · exact treeEq3273

theorem accepted3267 : B3267.accepted = true := by decide +kernel
theorem checked3267 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3267 (maskNeeds ![10387129018270111715863986064851329, 792633534417208834, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3267]
  exact B3267.sound accepted3267
#print axioms checked3267

end HexagonCover.NBand.M6900_7100.SplitTree.Run0043
