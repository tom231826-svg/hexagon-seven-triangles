import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0046
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0047
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3384_3385 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3385 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0046.checked3385
def B3507 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6373608640421845697769209617137366223595704740741184] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1150).pointIds 1150), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1151).pointIds 1151)]
theorem treeEq3507 : B3507.tree = HexagonCover.NBand.M6900_7100.SplitData.node3507 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3506 : Block := .branch 160 ![385, 748288838313422294120286634350884480016427138418178, 18446745173221185540, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6372147138784514794851005932304649940576048808198208] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1196).pointIds 1196), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B3507]
theorem treeEq3506 : B3506.tree = HexagonCover.NBand.M6900_7100.SplitData.node3506 := by
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
  · exact treeEq3507

def B3505 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B3506, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq3505 : B3505.tree = HexagonCover.NBand.M6900_7100.SplitData.node3505 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3506
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3504 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B3505]
theorem treeEq3504 : B3504.tree = HexagonCover.NBand.M6900_7100.SplitData.node3504 := by
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
  · exact treeEq3505

def B3503 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B3504, (.leaf 0 [] 0)]
theorem treeEq3503 : B3503.tree = HexagonCover.NBand.M6900_7100.SplitData.node3503 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3504
  · rfl

def B3502 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B3503, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3502 : B3502.tree = HexagonCover.NBand.M6900_7100.SplitData.node3502 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3503
  · rfl

def B3501 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B3502, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq3501 : B3501.tree = HexagonCover.NBand.M6900_7100.SplitData.node3501 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3502
  · rfl
  · rfl

def B3500 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3501, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq3500 : B3500.tree = HexagonCover.NBand.M6900_7100.SplitData.node3500 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3501
  · rfl

def B3499 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3500, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3499 : B3499.tree = HexagonCover.NBand.M6900_7100.SplitData.node3499 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3500
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3498 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3499]
theorem treeEq3498 : B3498.tree = HexagonCover.NBand.M6900_7100.SplitData.node3498 := by
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
  · exact treeEq3499

def B3497 : Block := .branch 171 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3498, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq3497 : B3497.tree = HexagonCover.NBand.M6900_7100.SplitData.node3497 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3498
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3496 : Block := .branch 151 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3497, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3496 : B3496.tree = HexagonCover.NBand.M6900_7100.SplitData.node3496 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3497
  · rfl

def B3495 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3496, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq3495 : B3495.tree = HexagonCover.NBand.M6900_7100.SplitData.node3495 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3496
  · rfl
  · rfl

def B3494 : Block := .branch 172 ![385, 147718067777752270338, 18446745173221185540, 79266857585224971466424999944, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3495]
theorem treeEq3494 : B3494.tree = HexagonCover.NBand.M6900_7100.SplitData.node3494 := by
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
  · exact treeEq3495

def B3384 : Block := .branch 73 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), Tip3384_3385, B3494, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq3384 : B3384.tree = HexagonCover.NBand.M6900_7100.SplitData.node3384 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3494
  · rfl
  · rfl
  · rfl

theorem accepted3384 : B3384.accepted = true := by decide +kernel
theorem checked3384 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3384 (maskNeeds ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3384]
  exact B3384.sound accepted3384
#print axioms checked3384

def Tip3383_3384 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3384 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3384
def B3521 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6373608640421845697769209617137366223595704740741184] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1150).pointIds 1150), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1151).pointIds 1151)]
theorem treeEq3521 : B3521.tree = HexagonCover.NBand.M6900_7100.SplitData.node3521 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3520 : Block := .branch 160 ![385, 748288838313422294120286634350884480016427138418178, 18446745173221185540, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6372147138784514794851005932304649940576048808198208] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1196).pointIds 1196), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B3521]
theorem treeEq3520 : B3520.tree = HexagonCover.NBand.M6900_7100.SplitData.node3520 := by
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
  · exact treeEq3521

def B3519 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B3520, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq3519 : B3519.tree = HexagonCover.NBand.M6900_7100.SplitData.node3519 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3520
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3518 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B3519]
theorem treeEq3518 : B3518.tree = HexagonCover.NBand.M6900_7100.SplitData.node3518 := by
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
  · exact treeEq3519

def B3517 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B3518, (.leaf 0 [] 0)]
theorem treeEq3517 : B3517.tree = HexagonCover.NBand.M6900_7100.SplitData.node3517 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3518
  · rfl

def B3516 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B3517, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3516 : B3516.tree = HexagonCover.NBand.M6900_7100.SplitData.node3516 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3517
  · rfl

def B3515 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B3516, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq3515 : B3515.tree = HexagonCover.NBand.M6900_7100.SplitData.node3515 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3516
  · rfl
  · rfl

def B3514 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3515, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq3514 : B3514.tree = HexagonCover.NBand.M6900_7100.SplitData.node3514 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3515
  · rfl

def B3513 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3514, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3513 : B3513.tree = HexagonCover.NBand.M6900_7100.SplitData.node3513 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3514
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3512 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3513]
theorem treeEq3512 : B3512.tree = HexagonCover.NBand.M6900_7100.SplitData.node3512 := by
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
  · exact treeEq3513

def B3511 : Block := .branch 171 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3512, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq3511 : B3511.tree = HexagonCover.NBand.M6900_7100.SplitData.node3511 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3512
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3510 : Block := .branch 151 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3511, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3510 : B3510.tree = HexagonCover.NBand.M6900_7100.SplitData.node3510 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3511
  · rfl

def B3509 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3510, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq3509 : B3509.tree = HexagonCover.NBand.M6900_7100.SplitData.node3509 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3510
  · rfl
  · rfl

def B3508 : Block := .branch 172 ![385, 147718067777752270338, 18446745173221185540, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1101).pointIds 1101), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3509]
theorem treeEq3508 : B3508.tree = HexagonCover.NBand.M6900_7100.SplitData.node3508 := by
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
  · exact treeEq3509

def B3383 : Block := .branch 72 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), Tip3383_3384, B3508, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq3383 : B3383.tree = HexagonCover.NBand.M6900_7100.SplitData.node3383 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3508
  · rfl
  · rfl
  · rfl

theorem accepted3383 : B3383.accepted = true := by decide +kernel
theorem checked3383 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3383 (maskNeeds ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3383]
  exact B3383.sound accepted3383
#print axioms checked3383

def B3544 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq3544 : B3544.tree = HexagonCover.NBand.M6900_7100.SplitData.node3544 := by
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

def B3543 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B3544, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq3543 : B3543.tree = HexagonCover.NBand.M6900_7100.SplitData.node3543 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3544
  · rfl
  · rfl

def B3542 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3543, (.leaf 6 (Common.fact 1154).pointIds 1154)]
theorem treeEq3542 : B3542.tree = HexagonCover.NBand.M6900_7100.SplitData.node3542 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3543
  · rfl

def B3541 : Block := .branch 166 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![B3542, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3541 : B3541.tree = HexagonCover.NBand.M6900_7100.SplitData.node3541 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3542
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3540 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 1073).pointIds 1073), B3541, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1114).pointIds 1114)]
theorem treeEq3540 : B3540.tree = HexagonCover.NBand.M6900_7100.SplitData.node3540 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3541
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3539 : Block := .branch 71 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), B3540, (.leaf 3 (Common.fact 1113).pointIds 1113), (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq3539 : B3539.tree = HexagonCover.NBand.M6900_7100.SplitData.node3539 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3540
  · rfl
  · rfl
  · rfl
  · rfl

def B3538 : Block := .branch 72 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B3539, (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq3538 : B3538.tree = HexagonCover.NBand.M6900_7100.SplitData.node3538 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3539
  · rfl
  · rfl
  · rfl
  · rfl

def B3537 : Block := .branch 73 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B3538, (.leaf 3 (Common.fact 1111).pointIds 1111), (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq3537 : B3537.tree = HexagonCover.NBand.M6900_7100.SplitData.node3537 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3538
  · rfl
  · rfl
  · rfl
  · rfl

def B3536 : Block := .branch 74 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B3537, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq3536 : B3536.tree = HexagonCover.NBand.M6900_7100.SplitData.node3536 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3537
  · rfl
  · rfl
  · rfl
  · rfl

def B3535 : Block := .branch 75 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), B3536, (.leaf 3 (Common.fact 1109).pointIds 1109), (.leaf 4 (Common.fact 988).pointIds 988), (.leaf 5 (Common.fact 989).pointIds 989), (.leaf 6 (Common.fact 1110).pointIds 1110)]
theorem treeEq3535 : B3535.tree = HexagonCover.NBand.M6900_7100.SplitData.node3535 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3536
  · rfl
  · rfl
  · rfl
  · rfl

def B3534 : Block := .branch 172 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 2923003274661805836407369665432566039311865110536, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3535]
theorem treeEq3534 : B3534.tree = HexagonCover.NBand.M6900_7100.SplitData.node3534 := by
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
  · exact treeEq3535

def B3533 : Block := .branch 161 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 24584, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), B3534, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1108).pointIds 1108)]
theorem treeEq3533 : B3533.tree = HexagonCover.NBand.M6900_7100.SplitData.node3533 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3534
  · rfl
  · rfl
  · rfl

def B3532 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 24584, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3533]
theorem treeEq3532 : B3532.tree = HexagonCover.NBand.M6900_7100.SplitData.node3532 := by
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
  · exact treeEq3533

def B3531 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![B3532, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq3531 : B3531.tree = HexagonCover.NBand.M6900_7100.SplitData.node3531 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3530 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3531, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3530 : B3530.tree = HexagonCover.NBand.M6900_7100.SplitData.node3530 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3531
  · rfl

def B3529 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3530, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1106).pointIds 1106)]
theorem treeEq3529 : B3529.tree = HexagonCover.NBand.M6900_7100.SplitData.node3529 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3530
  · rfl
  · rfl

theorem accepted3529 : B3529.accepted = true := by decide +kernel
theorem checked3529 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3529 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488]) := by
  rw [← treeEq3529]
  exact B3529.sound accepted3529
#print axioms checked3529

def B3562 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 1496577682202030887873229054085403380289765300600848, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 1079).pointIds 1079), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 1161).pointIds 1161)]
theorem treeEq3562 : B3562.tree = HexagonCover.NBand.M6900_7100.SplitData.node3562 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3561 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B3562, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1160).pointIds 1160)]
theorem treeEq3561 : B3561.tree = HexagonCover.NBand.M6900_7100.SplitData.node3561 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3562
  · rfl
  · rfl

def B3560 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3561, (.leaf 6 (Common.fact 1159).pointIds 1159)]
theorem treeEq3560 : B3560.tree = HexagonCover.NBand.M6900_7100.SplitData.node3560 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3561
  · rfl

def B3559 : Block := .branch 166 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![B3560, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3559 : B3559.tree = HexagonCover.NBand.M6900_7100.SplitData.node3559 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3560
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3558 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 1073).pointIds 1073), B3559, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1121).pointIds 1121)]
theorem treeEq3558 : B3558.tree = HexagonCover.NBand.M6900_7100.SplitData.node3558 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3559
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3557 : Block := .branch 71 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), B3558, (.leaf 3 (Common.fact 1113).pointIds 1113), (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq3557 : B3557.tree = HexagonCover.NBand.M6900_7100.SplitData.node3557 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3558
  · rfl
  · rfl
  · rfl
  · rfl

def B3556 : Block := .branch 72 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B3557, (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq3556 : B3556.tree = HexagonCover.NBand.M6900_7100.SplitData.node3556 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3557
  · rfl
  · rfl
  · rfl
  · rfl

def B3555 : Block := .branch 73 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B3556, (.leaf 3 (Common.fact 1111).pointIds 1111), (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq3555 : B3555.tree = HexagonCover.NBand.M6900_7100.SplitData.node3555 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3556
  · rfl
  · rfl
  · rfl
  · rfl

def B3554 : Block := .branch 74 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B3555, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq3554 : B3554.tree = HexagonCover.NBand.M6900_7100.SplitData.node3554 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3555
  · rfl
  · rfl
  · rfl
  · rfl

def B3553 : Block := .branch 75 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), B3554, (.leaf 3 (Common.fact 1109).pointIds 1109), (.leaf 4 (Common.fact 988).pointIds 988), (.leaf 5 (Common.fact 989).pointIds 989), (.leaf 6 (Common.fact 1158).pointIds 1158)]
theorem treeEq3553 : B3553.tree = HexagonCover.NBand.M6900_7100.SplitData.node3553 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3554
  · rfl
  · rfl
  · rfl
  · rfl

def B3552 : Block := .branch 172 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3553]
theorem treeEq3552 : B3552.tree = HexagonCover.NBand.M6900_7100.SplitData.node3552 := by
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
  · exact treeEq3553

def B3551 : Block := .branch 161 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038204319543163511898176] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), B3552, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1157).pointIds 1157)]
theorem treeEq3551 : B3551.tree = HexagonCover.NBand.M6900_7100.SplitData.node3551 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3552
  · rfl
  · rfl
  · rfl

def B3550 : Block := .branch 66 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350737050179025537861122, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038204319543163511898176] ![(.leaf 0 (Common.fact 902).pointIds 902), (.leaf 1 (Common.fact 1198).pointIds 1198), B3551, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 904).pointIds 904), (.leaf 5 (Common.fact 905).pointIds 905), (.leaf 6 (Common.fact 1156).pointIds 1156)]
theorem treeEq3550 : B3550.tree = HexagonCover.NBand.M6900_7100.SplitData.node3550 := by
  change Tree.branch (66 : Fin 173) _ = Tree.branch (66 : Fin 173) _
  apply congrArg (Tree.branch (66 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3551
  · rfl
  · rfl
  · rfl
  · rfl

def B3549 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038204319543163511898176] ![(.leaf 0 (Common.fact 928).pointIds 928), B3550, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1120).pointIds 1120)]
theorem treeEq3549 : B3549.tree = HexagonCover.NBand.M6900_7100.SplitData.node3549 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3550
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3548 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3549]
theorem treeEq3548 : B3548.tree = HexagonCover.NBand.M6900_7100.SplitData.node3548 := by
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
  · exact treeEq3549

def B3547 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![B3548, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1119).pointIds 1119)]
theorem treeEq3547 : B3547.tree = HexagonCover.NBand.M6900_7100.SplitData.node3547 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3548
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3546 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3547, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3546 : B3546.tree = HexagonCover.NBand.M6900_7100.SplitData.node3546 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3547
  · rfl

def B3545 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3546, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1118).pointIds 1118)]
theorem treeEq3545 : B3545.tree = HexagonCover.NBand.M6900_7100.SplitData.node3545 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3546
  · rfl
  · rfl

theorem accepted3545 : B3545.accepted = true := by decide +kernel
theorem checked3545 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3545 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560]) := by
  rw [← treeEq3545]
  exact B3545.sound accepted3545
#print axioms checked3545

def Tip3379_3383 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3383 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3383
def Tip3379_3529 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3529 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] checked3529
def Tip3379_3545 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3545 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] checked3545
def B3528 : Block := .branch 89 ![385, 748288838313422294120286634350884480016427138418178, 6148, 24584, 98320, 393248, 400451448650445471071066927960984400957351338180672] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 1197).pointIds 1197), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), (.leaf 6 (Common.fact 1153).pointIds 1153)]
theorem treeEq3528 : B3528.tree = HexagonCover.NBand.M6900_7100.SplitData.node3528 := by
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

def B3527 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 400451448650445471071066927960984400957351338180672] ![(.leaf 0 (Common.fact 928).pointIds 928), B3528, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1104).pointIds 1104)]
theorem treeEq3527 : B3527.tree = HexagonCover.NBand.M6900_7100.SplitData.node3527 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3528
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3526 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379807970637523872642856417493056] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3527]
theorem treeEq3526 : B3526.tree = HexagonCover.NBand.M6900_7100.SplitData.node3526 := by
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
  · exact treeEq3527

def B3525 : Block := .branch 171 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 377067422453151024379807970637523872642856417493056] ![B3526, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq3525 : B3525.tree = HexagonCover.NBand.M6900_7100.SplitData.node3525 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3526
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3524 : Block := .branch 151 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3525, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3524 : B3524.tree = HexagonCover.NBand.M6900_7100.SplitData.node3524 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3525
  · rfl

def B3523 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3524, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1102).pointIds 1102)]
theorem treeEq3523 : B3523.tree = HexagonCover.NBand.M6900_7100.SplitData.node3523 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3524
  · rfl
  · rfl

def B3522 : Block := .branch 161 ![385, 147718067777752270338, 18446745173221185540, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), B3523]
theorem treeEq3522 : B3522.tree = HexagonCover.NBand.M6900_7100.SplitData.node3522 := by
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
  · exact treeEq3523

def B3382 : Block := .branch 71 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), Tip3379_3383, B3522, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq3382 : B3382.tree = HexagonCover.NBand.M6900_7100.SplitData.node3382 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3522
  · rfl
  · rfl
  · rfl

def B3381 : Block := .branch 68 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 445).pointIds 445), B3382, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), Tip3379_3529]
theorem treeEq3381 : B3381.tree = HexagonCover.NBand.M6900_7100.SplitData.node3381 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3382
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3380 : Block := .branch 67 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 439).pointIds 439), B3381, (.leaf 2 (Common.fact 440).pointIds 440), (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), Tip3379_3545]
theorem treeEq3380 : B3380.tree = HexagonCover.NBand.M6900_7100.SplitData.node3380 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3381
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3567 : Block := .branch 89 ![385, 748288838313422294120286634350736906063837462005250, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 1192).pointIds 1192), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), (.leaf 6 (Common.fact 1162).pointIds 1162)]
theorem treeEq3567 : B3567.tree = HexagonCover.NBand.M6900_7100.SplitData.node3567 := by
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

def B3566 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 1538, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 928).pointIds 928), B3567, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq3566 : B3566.tree = HexagonCover.NBand.M6900_7100.SplitData.node3566 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3567
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3565 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974311749925714704515727424] ![B3566, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq3565 : B3565.tree = HexagonCover.NBand.M6900_7100.SplitData.node3565 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3566
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3564 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3565, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3564 : B3564.tree = HexagonCover.NBand.M6900_7100.SplitData.node3564 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3565
  · rfl

def B3563 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3564, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq3563 : B3563.tree = HexagonCover.NBand.M6900_7100.SplitData.node3563 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3564
  · rfl
  · rfl

def B3379 : Block := .branch 65 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), B3380, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B3563]
theorem treeEq3379 : B3379.tree = HexagonCover.NBand.M6900_7100.SplitData.node3379 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3380
  · rfl
  · rfl
  · rfl
  · exact treeEq3563

theorem accepted3379 : B3379.accepted = true := by decide +kernel
theorem checked3379 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3379 (maskNeeds ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3379]
  exact B3379.sound accepted3379
#print axioms checked3379

end HexagonCover.NBand.M6900_7100.SplitTree.Run0047
