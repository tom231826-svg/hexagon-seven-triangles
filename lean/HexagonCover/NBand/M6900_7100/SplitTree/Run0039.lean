import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0038
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0039
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2761_2762 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2762 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0038.checked2762
def B2884 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6373608640421845697769209617137366223595704740741184] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1150).pointIds 1150), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1151).pointIds 1151)]
theorem treeEq2884 : B2884.tree = HexagonCover.NBand.M6900_7100.SplitData.node2884 := by
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

def B2883 : Block := .branch 160 ![385, 748288838313422294120286634350884480017526650045954, 18446884811197913092, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6372147138784514794851005932304649940576048808198208] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1149).pointIds 1149), (.leaf 2 (Common.fact 1138).pointIds 1138), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2884]
theorem treeEq2883 : B2883.tree = HexagonCover.NBand.M6900_7100.SplitData.node2883 := by
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
  · exact treeEq2884

def B2882 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B2883, (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq2882 : B2882.tree = HexagonCover.NBand.M6900_7100.SplitData.node2882 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2883
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2881 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2882]
theorem treeEq2881 : B2881.tree = HexagonCover.NBand.M6900_7100.SplitData.node2881 := by
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
  · exact treeEq2882

def B2880 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2881, (.leaf 0 [] 0)]
theorem treeEq2880 : B2880.tree = HexagonCover.NBand.M6900_7100.SplitData.node2880 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2881
  · rfl

def B2879 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2880, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2879 : B2879.tree = HexagonCover.NBand.M6900_7100.SplitData.node2879 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2880
  · rfl

def B2878 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2879, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq2878 : B2878.tree = HexagonCover.NBand.M6900_7100.SplitData.node2878 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2879
  · rfl
  · rfl

def B2877 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2878, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq2877 : B2877.tree = HexagonCover.NBand.M6900_7100.SplitData.node2877 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2878
  · rfl

def B2876 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2877, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2876 : B2876.tree = HexagonCover.NBand.M6900_7100.SplitData.node2876 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2877
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2875 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2876]
theorem treeEq2875 : B2875.tree = HexagonCover.NBand.M6900_7100.SplitData.node2875 := by
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
  · exact treeEq2876

def B2874 : Block := .branch 171 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2875, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2874 : B2874.tree = HexagonCover.NBand.M6900_7100.SplitData.node2874 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2875
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2873 : Block := .branch 151 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2874, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2873 : B2873.tree = HexagonCover.NBand.M6900_7100.SplitData.node2873 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2874
  · rfl

def B2872 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2873, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2872 : B2872.tree = HexagonCover.NBand.M6900_7100.SplitData.node2872 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2873
  · rfl
  · rfl

def B2871 : Block := .branch 172 ![385, 147718068877263898114, 18446884811197913092, 79266857585224971466424999944, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2872]
theorem treeEq2871 : B2871.tree = HexagonCover.NBand.M6900_7100.SplitData.node2871 := by
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
  · exact treeEq2872

def B2761 : Block := .branch 73 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), Tip2761_2762, B2871, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq2761 : B2761.tree = HexagonCover.NBand.M6900_7100.SplitData.node2761 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2871
  · rfl
  · rfl
  · rfl

theorem accepted2761 : B2761.accepted = true := by decide +kernel
theorem checked2761 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2761 (maskNeeds ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2761]
  exact B2761.sound accepted2761
#print axioms checked2761

def Tip2760_2761 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2761 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2761
def B2898 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6373608640421845697769209617137366223595704740741184] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1150).pointIds 1150), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1151).pointIds 1151)]
theorem treeEq2898 : B2898.tree = HexagonCover.NBand.M6900_7100.SplitData.node2898 := by
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

def B2897 : Block := .branch 160 ![385, 748288838313422294120286634350884480017526650045954, 18446884811197913092, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6372147138784514794851005932304649940576048808198208] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1149).pointIds 1149), (.leaf 2 (Common.fact 1138).pointIds 1138), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2898]
theorem treeEq2897 : B2897.tree = HexagonCover.NBand.M6900_7100.SplitData.node2897 := by
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
  · exact treeEq2898

def B2896 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B2897, (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq2896 : B2896.tree = HexagonCover.NBand.M6900_7100.SplitData.node2896 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2897
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2895 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2896]
theorem treeEq2895 : B2895.tree = HexagonCover.NBand.M6900_7100.SplitData.node2895 := by
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
  · exact treeEq2896

def B2894 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2895, (.leaf 0 [] 0)]
theorem treeEq2894 : B2894.tree = HexagonCover.NBand.M6900_7100.SplitData.node2894 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2895
  · rfl

def B2893 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2894, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2893 : B2893.tree = HexagonCover.NBand.M6900_7100.SplitData.node2893 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2894
  · rfl

def B2892 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2893, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq2892 : B2892.tree = HexagonCover.NBand.M6900_7100.SplitData.node2892 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2893
  · rfl
  · rfl

def B2891 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2892, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq2891 : B2891.tree = HexagonCover.NBand.M6900_7100.SplitData.node2891 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2892
  · rfl

def B2890 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2891, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2890 : B2890.tree = HexagonCover.NBand.M6900_7100.SplitData.node2890 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2891
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2889 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2890]
theorem treeEq2889 : B2889.tree = HexagonCover.NBand.M6900_7100.SplitData.node2889 := by
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
  · exact treeEq2890

def B2888 : Block := .branch 171 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2889, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2888 : B2888.tree = HexagonCover.NBand.M6900_7100.SplitData.node2888 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2889
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2887 : Block := .branch 151 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2888, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2887 : B2887.tree = HexagonCover.NBand.M6900_7100.SplitData.node2887 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2888
  · rfl

def B2886 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2887, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2886 : B2886.tree = HexagonCover.NBand.M6900_7100.SplitData.node2886 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2887
  · rfl
  · rfl

def B2885 : Block := .branch 172 ![385, 147718068877263898114, 18446884811197913092, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1101).pointIds 1101), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2886]
theorem treeEq2885 : B2885.tree = HexagonCover.NBand.M6900_7100.SplitData.node2885 := by
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
  · exact treeEq2886

def B2760 : Block := .branch 72 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), Tip2760_2761, B2885, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq2760 : B2760.tree = HexagonCover.NBand.M6900_7100.SplitData.node2760 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2885
  · rfl
  · rfl
  · rfl

theorem accepted2760 : B2760.accepted = true := by decide +kernel
theorem checked2760 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2760 (maskNeeds ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2760]
  exact B2760.sound accepted2760
#print axioms checked2760

def B2921 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq2921 : B2921.tree = HexagonCover.NBand.M6900_7100.SplitData.node2921 := by
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

def B2920 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2921, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2920 : B2920.tree = HexagonCover.NBand.M6900_7100.SplitData.node2920 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2921
  · rfl
  · rfl

def B2919 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2920, (.leaf 6 (Common.fact 1154).pointIds 1154)]
theorem treeEq2919 : B2919.tree = HexagonCover.NBand.M6900_7100.SplitData.node2919 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2920
  · rfl

def B2918 : Block := .branch 166 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![B2919, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2918 : B2918.tree = HexagonCover.NBand.M6900_7100.SplitData.node2918 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2919
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2917 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 1073).pointIds 1073), B2918, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1114).pointIds 1114)]
theorem treeEq2917 : B2917.tree = HexagonCover.NBand.M6900_7100.SplitData.node2917 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2918
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2916 : Block := .branch 71 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), B2917, (.leaf 3 (Common.fact 1113).pointIds 1113), (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq2916 : B2916.tree = HexagonCover.NBand.M6900_7100.SplitData.node2916 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2917
  · rfl
  · rfl
  · rfl
  · rfl

def B2915 : Block := .branch 72 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B2916, (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq2915 : B2915.tree = HexagonCover.NBand.M6900_7100.SplitData.node2915 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2916
  · rfl
  · rfl
  · rfl
  · rfl

def B2914 : Block := .branch 73 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B2915, (.leaf 3 (Common.fact 1111).pointIds 1111), (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq2914 : B2914.tree = HexagonCover.NBand.M6900_7100.SplitData.node2914 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2915
  · rfl
  · rfl
  · rfl
  · rfl

def B2913 : Block := .branch 74 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B2914, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq2913 : B2913.tree = HexagonCover.NBand.M6900_7100.SplitData.node2913 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2914
  · rfl
  · rfl
  · rfl
  · rfl

def B2912 : Block := .branch 75 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407369665432566039311865110536, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), B2913, (.leaf 3 (Common.fact 1109).pointIds 1109), (.leaf 4 (Common.fact 988).pointIds 988), (.leaf 5 (Common.fact 989).pointIds 989), (.leaf 6 (Common.fact 1110).pointIds 1110)]
theorem treeEq2912 : B2912.tree = HexagonCover.NBand.M6900_7100.SplitData.node2912 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2913
  · rfl
  · rfl
  · rfl
  · rfl

def B2911 : Block := .branch 172 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 2923003274661805836407369665432566039311865110536, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2912]
theorem treeEq2911 : B2911.tree = HexagonCover.NBand.M6900_7100.SplitData.node2911 := by
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
  · exact treeEq2912

def B2910 : Block := .branch 161 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 24584, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038351893495753188311104] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), B2911, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1108).pointIds 1108)]
theorem treeEq2910 : B2910.tree = HexagonCover.NBand.M6900_7100.SplitData.node2910 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2911
  · rfl
  · rfl
  · rfl

def B2909 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 24584, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2910]
theorem treeEq2909 : B2909.tree = HexagonCover.NBand.M6900_7100.SplitData.node2909 := by
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
  · exact treeEq2910

def B2908 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714891365181258267623488] ![B2909, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq2908 : B2908.tree = HexagonCover.NBand.M6900_7100.SplitData.node2908 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2909
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2907 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2908, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2907 : B2907.tree = HexagonCover.NBand.M6900_7100.SplitData.node2907 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2908
  · rfl

def B2906 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2907, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1106).pointIds 1106)]
theorem treeEq2906 : B2906.tree = HexagonCover.NBand.M6900_7100.SplitData.node2906 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2907
  · rfl
  · rfl

theorem accepted2906 : B2906.accepted = true := by decide +kernel
theorem checked2906 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2906 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488]) := by
  rw [← treeEq2906]
  exact B2906.sound accepted2906
#print axioms checked2906

def B2939 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 1496577682202030887873229054085403380289765300600848, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 1079).pointIds 1079), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 1161).pointIds 1161)]
theorem treeEq2939 : B2939.tree = HexagonCover.NBand.M6900_7100.SplitData.node2939 := by
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

def B2938 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2939, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1160).pointIds 1160)]
theorem treeEq2938 : B2938.tree = HexagonCover.NBand.M6900_7100.SplitData.node2938 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2939
  · rfl
  · rfl

def B2937 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2938, (.leaf 6 (Common.fact 1159).pointIds 1159)]
theorem treeEq2937 : B2937.tree = HexagonCover.NBand.M6900_7100.SplitData.node2937 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2938
  · rfl

def B2936 : Block := .branch 166 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![B2937, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2936 : B2936.tree = HexagonCover.NBand.M6900_7100.SplitData.node2936 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2937
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2935 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 1073).pointIds 1073), B2936, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1121).pointIds 1121)]
theorem treeEq2935 : B2935.tree = HexagonCover.NBand.M6900_7100.SplitData.node2935 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2936
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2934 : Block := .branch 71 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), B2935, (.leaf 3 (Common.fact 1113).pointIds 1113), (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq2934 : B2934.tree = HexagonCover.NBand.M6900_7100.SplitData.node2934 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2935
  · rfl
  · rfl
  · rfl
  · rfl

def B2933 : Block := .branch 72 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B2934, (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq2933 : B2933.tree = HexagonCover.NBand.M6900_7100.SplitData.node2933 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2934
  · rfl
  · rfl
  · rfl
  · rfl

def B2932 : Block := .branch 73 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), B2933, (.leaf 3 (Common.fact 1111).pointIds 1111), (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq2932 : B2932.tree = HexagonCover.NBand.M6900_7100.SplitData.node2932 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2933
  · rfl
  · rfl
  · rfl
  · rfl

def B2931 : Block := .branch 74 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B2932, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq2931 : B2931.tree = HexagonCover.NBand.M6900_7100.SplitData.node2931 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2932
  · rfl
  · rfl
  · rfl
  · rfl

def B2930 : Block := .branch 75 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 2923003274661805836407408351058793707445455708168, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), B2931, (.leaf 3 (Common.fact 1109).pointIds 1109), (.leaf 4 (Common.fact 988).pointIds 988), (.leaf 5 (Common.fact 989).pointIds 989), (.leaf 6 (Common.fact 1158).pointIds 1158)]
theorem treeEq2930 : B2930.tree = HexagonCover.NBand.M6900_7100.SplitData.node2930 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2931
  · rfl
  · rfl
  · rfl
  · rfl

def B2929 : Block := .branch 172 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2930]
theorem treeEq2929 : B2929.tree = HexagonCover.NBand.M6900_7100.SplitData.node2929 := by
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
  · exact treeEq2930

def B2928 : Block := .branch 161 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038204319543163511898176] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), B2929, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1157).pointIds 1157)]
theorem treeEq2928 : B2928.tree = HexagonCover.NBand.M6900_7100.SplitData.node2928 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2929
  · rfl
  · rfl
  · rfl

def B2927 : Block := .branch 66 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350737050180125049488898, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038204319543163511898176] ![(.leaf 0 (Common.fact 902).pointIds 902), (.leaf 1 (Common.fact 1155).pointIds 1155), B2928, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 904).pointIds 904), (.leaf 5 (Common.fact 905).pointIds 905), (.leaf 6 (Common.fact 1156).pointIds 1156)]
theorem treeEq2927 : B2927.tree = HexagonCover.NBand.M6900_7100.SplitData.node2927 := by
  change Tree.branch (66 : Fin 173) _ = Tree.branch (66 : Fin 173) _
  apply congrArg (Tree.branch (66 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2928
  · rfl
  · rfl
  · rfl
  · rfl

def B2926 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713038204319543163511898176] ![(.leaf 0 (Common.fact 928).pointIds 928), B2927, (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1120).pointIds 1120)]
theorem treeEq2926 : B2926.tree = HexagonCover.NBand.M6900_7100.SplitData.node2926 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2927
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2925 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2926]
theorem treeEq2925 : B2925.tree = HexagonCover.NBand.M6900_7100.SplitData.node2925 := by
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
  · exact treeEq2926

def B2924 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714743791228668591210560] ![B2925, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1119).pointIds 1119)]
theorem treeEq2924 : B2924.tree = HexagonCover.NBand.M6900_7100.SplitData.node2924 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2925
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2923 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2924, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2923 : B2923.tree = HexagonCover.NBand.M6900_7100.SplitData.node2923 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2924
  · rfl

def B2922 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2923, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1118).pointIds 1118)]
theorem treeEq2922 : B2922.tree = HexagonCover.NBand.M6900_7100.SplitData.node2922 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2923
  · rfl
  · rfl

theorem accepted2922 : B2922.accepted = true := by decide +kernel
theorem checked2922 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2922 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560]) := by
  rw [← treeEq2922]
  exact B2922.sound accepted2922
#print axioms checked2922

def Tip2756_2760 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2760 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2760
def Tip2756_2906 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2906 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] checked2906
def Tip2756_2922 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2922 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] checked2922
def B2905 : Block := .branch 89 ![385, 748288838313422294120286634350884480017526650045954, 6148, 24584, 98320, 393248, 400451448650445471071066927960984400957351338180672] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 1152).pointIds 1152), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), (.leaf 6 (Common.fact 1153).pointIds 1153)]
theorem treeEq2905 : B2905.tree = HexagonCover.NBand.M6900_7100.SplitData.node2905 := by
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

def B2904 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 400451448650445471071066927960984400957351338180672] ![(.leaf 0 (Common.fact 928).pointIds 928), B2905, (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1104).pointIds 1104)]
theorem treeEq2904 : B2904.tree = HexagonCover.NBand.M6900_7100.SplitData.node2904 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2905
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2903 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379807970637523872642856417493056] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2904]
theorem treeEq2903 : B2903.tree = HexagonCover.NBand.M6900_7100.SplitData.node2903 := by
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
  · exact treeEq2904

def B2902 : Block := .branch 171 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 377067422453151024379807970637523872642856417493056] ![B2903, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq2902 : B2902.tree = HexagonCover.NBand.M6900_7100.SplitData.node2902 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2903
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2901 : Block := .branch 151 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2902, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2901 : B2901.tree = HexagonCover.NBand.M6900_7100.SplitData.node2901 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2902
  · rfl

def B2900 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2901, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1102).pointIds 1102)]
theorem treeEq2900 : B2900.tree = HexagonCover.NBand.M6900_7100.SplitData.node2900 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2901
  · rfl
  · rfl

def B2899 : Block := .branch 161 ![385, 147718068877263898114, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), B2900]
theorem treeEq2899 : B2899.tree = HexagonCover.NBand.M6900_7100.SplitData.node2899 := by
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
  · exact treeEq2900

def B2759 : Block := .branch 71 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), Tip2756_2760, B2899, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq2759 : B2759.tree = HexagonCover.NBand.M6900_7100.SplitData.node2759 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2899
  · rfl
  · rfl
  · rfl

def B2758 : Block := .branch 68 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 445).pointIds 445), B2759, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), Tip2756_2906]
theorem treeEq2758 : B2758.tree = HexagonCover.NBand.M6900_7100.SplitData.node2758 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2759
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2757 : Block := .branch 67 ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 439).pointIds 439), B2758, (.leaf 2 (Common.fact 440).pointIds 440), (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), Tip2756_2922]
theorem treeEq2757 : B2757.tree = HexagonCover.NBand.M6900_7100.SplitData.node2757 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2758
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2944 : Block := .branch 89 ![385, 748288838313422294120286634350736906064936973633026, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 1049).pointIds 1049), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), (.leaf 6 (Common.fact 1162).pointIds 1162)]
theorem treeEq2944 : B2944.tree = HexagonCover.NBand.M6900_7100.SplitData.node2944 := by
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

def B2943 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 928).pointIds 928), B2944, (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq2943 : B2943.tree = HexagonCover.NBand.M6900_7100.SplitData.node2943 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2944
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2942 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483256974311749925714704515727424] ![B2943, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq2942 : B2942.tree = HexagonCover.NBand.M6900_7100.SplitData.node2942 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2943
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2941 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2942, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2941 : B2941.tree = HexagonCover.NBand.M6900_7100.SplitData.node2941 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2942
  · rfl

def B2940 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714633110764226333900864] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2941, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq2940 : B2940.tree = HexagonCover.NBand.M6900_7100.SplitData.node2940 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2941
  · rfl
  · rfl

def B2756 : Block := .branch 65 ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), B2757, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), B2940]
theorem treeEq2756 : B2756.tree = HexagonCover.NBand.M6900_7100.SplitData.node2756 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2757
  · rfl
  · rfl
  · rfl
  · exact treeEq2940

theorem accepted2756 : B2756.accepted = true := by decide +kernel
theorem checked2756 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2756 (maskNeeds ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2756]
  exact B2756.sound accepted2756
#print axioms checked2756

end HexagonCover.NBand.M6900_7100.SplitTree.Run0039
