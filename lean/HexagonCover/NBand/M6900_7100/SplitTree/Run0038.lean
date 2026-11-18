import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0037
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0038
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2765_2767 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2767 ![10384593717069655257060992658440577, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0037.checked2767
def Tip2765_2803 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2803 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] HexagonCover.NBand.M6900_7100.SplitTree.Run0037.checked2803
def B2802 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 5444517870735015415413993718908291481616, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1069).pointIds 1069), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1070).pointIds 1070)]
theorem treeEq2802 : B2802.tree = HexagonCover.NBand.M6900_7100.SplitData.node2802 := by
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

def B2801 : Block := .branch 132 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), B2802, (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1068).pointIds 1068)]
theorem treeEq2801 : B2801.tree = HexagonCover.NBand.M6900_7100.SplitData.node2801 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2802
  · rfl
  · rfl

def B2800 : Block := .branch 143 ![385, 1538, 6148, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2801, (.leaf 6 (Common.fact 1067).pointIds 1067)]
theorem treeEq2800 : B2800.tree = HexagonCover.NBand.M6900_7100.SplitData.node2800 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2801
  · rfl

def B2799 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 2923003274661805836486597827946830376905409060872, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234342955130504598912734022074432] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2800]
theorem treeEq2799 : B2799.tree = HexagonCover.NBand.M6900_7100.SplitData.node2799 := by
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
  · exact treeEq2800

def B2798 : Block := .branch 161 ![385, 144116287587485186, 18446884811197913092, 79228162514264337593543974920, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234660022523066566935642560266304] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), B2799, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1065).pointIds 1065)]
theorem treeEq2798 : B2798.tree = HexagonCover.NBand.M6900_7100.SplitData.node2798 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2799
  · rfl
  · rfl
  · rfl

def B2797 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 79228162514264337593543974920, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2798]
theorem treeEq2797 : B2797.tree = HexagonCover.NBand.M6900_7100.SplitData.node2797 := by
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
  · exact treeEq2798

def B2796 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401065199606038621147639578688] ![B2797, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq2796 : B2796.tree = HexagonCover.NBand.M6900_7100.SplitData.node2796 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2797
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2795 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2796, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2795 : B2795.tree = HexagonCover.NBand.M6900_7100.SplitData.node2795 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2796
  · rfl

def B2794 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2795, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq2794 : B2794.tree = HexagonCover.NBand.M6900_7100.SplitData.node2794 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2795
  · rfl
  · rfl

def B2766 : Block := .branch 89 ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip2765_2767, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2794]
theorem treeEq2766 : B2766.tree = HexagonCover.NBand.M6900_7100.SplitData.node2766 := by
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
  · exact treeEq2794

def B2765 : Block := .branch 86 ![10384593717069655257060992658440577, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B2766, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), Tip2765_2803]
theorem treeEq2765 : B2765.tree = HexagonCover.NBand.M6900_7100.SplitData.node2765 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2766
  · rfl
  · rfl
  · rfl

theorem accepted2765 : B2765.accepted = true := by decide +kernel
theorem checked2765 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2765 (maskNeeds ![10384593717069655257060992658440577, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2765]
  exact B2765.sound accepted2765
#print axioms checked2765

def B2835 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293113491521476178833286651912, 98320, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1081).pointIds 1081), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1082).pointIds 1082)]
theorem treeEq2835 : B2835.tree = HexagonCover.NBand.M6900_7100.SplitData.node2835 := by
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

def B2834 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2835, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2834 : B2834.tree = HexagonCover.NBand.M6900_7100.SplitData.node2834 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2835
  · rfl
  · rfl
  · rfl

def B2833 : Block := .branch 124 ![10387129018874574625671300652204417, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 1080).pointIds 1080), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B2834]
theorem treeEq2833 : B2833.tree = HexagonCover.NBand.M6900_7100.SplitData.node2833 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2834

def B2843 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 1461501659108975050497766536840632538439393738816] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1087).pointIds 1087)]
theorem treeEq2843 : B2843.tree = HexagonCover.NBand.M6900_7100.SplitData.node2843 := by
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
  · rfl

def B2842 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2843, (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2842 : B2842.tree = HexagonCover.NBand.M6900_7100.SplitData.node2842 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2843
  · rfl
  · rfl

def B2841 : Block := .branch 132 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B2842]
theorem treeEq2841 : B2841.tree = HexagonCover.NBand.M6900_7100.SplitData.node2841 := by
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
  · exact treeEq2842

def B2840 : Block := .branch 86 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920826709157852111578770551805025777794678848] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B2841, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), (.leaf 6 (Common.fact 1086).pointIds 1086)]
theorem treeEq2840 : B2840.tree = HexagonCover.NBand.M6900_7100.SplitData.node2840 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2841
  · rfl
  · rfl
  · rfl

def B2839 : Block := .branch 133 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2840]
theorem treeEq2839 : B2839.tree = HexagonCover.NBand.M6900_7100.SplitData.node2839 := by
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
  · exact treeEq2840

def B2838 : Block := .branch 157 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2839, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2838 : B2838.tree = HexagonCover.NBand.M6900_7100.SplitData.node2838 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2839
  · rfl
  · rfl

def B2837 : Block := .branch 171 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2838, (.leaf 6 (Common.fact 1085).pointIds 1085)]
theorem treeEq2837 : B2837.tree = HexagonCover.NBand.M6900_7100.SplitData.node2837 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2838
  · rfl

def B2836 : Block := .branch 160 ![10384593717070245552871351364092289, 906694508827259468514818, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 1138).pointIds 1138), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2837]
theorem treeEq2836 : B2836.tree = HexagonCover.NBand.M6900_7100.SplitData.node2836 := by
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
  · exact treeEq2837

def B2832 : Block := .branch 79 ![10387129018270702011674344770503041, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B2833, B2836, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq2832 : B2832.tree = HexagonCover.NBand.M6900_7100.SplitData.node2832 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2833
  · exact treeEq2836
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2846 : Block := .branch 132 ![385, 1538, 6148, 24584, 184114952359068824656518890058984872593374412816, 393248, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq2846 : B2846.tree = HexagonCover.NBand.M6900_7100.SplitData.node2846 := by
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

def B2845 : Block := .branch 157 ![385, 1538, 6148, 24584, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2846, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2845 : B2845.tree = HexagonCover.NBand.M6900_7100.SplitData.node2845 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2846
  · rfl
  · rfl

def B2844 : Block := .branch 171 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2845, (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq2844 : B2844.tree = HexagonCover.NBand.M6900_7100.SplitData.node2844 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2845
  · rfl

def B2831 : Block := .branch 78 ![10387129018270702011674344770503041, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B2832, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2844]
theorem treeEq2831 : B2831.tree = HexagonCover.NBand.M6900_7100.SplitData.node2831 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2832
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2844

def B2830 : Block := .branch 101 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B2831, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq2830 : B2830.tree = HexagonCover.NBand.M6900_7100.SplitData.node2830 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2831
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2829 : Block := .branch 109 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2830]
theorem treeEq2829 : B2829.tree = HexagonCover.NBand.M6900_7100.SplitData.node2829 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2830

def B2828 : Block := .branch 150 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2829, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2828 : B2828.tree = HexagonCover.NBand.M6900_7100.SplitData.node2828 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2829
  · rfl
  · rfl

def B2827 : Block := .branch 125 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B2828, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2827 : B2827.tree = HexagonCover.NBand.M6900_7100.SplitData.node2827 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2828
  · rfl

theorem accepted2827 : B2827.accepted = true := by decide +kernel
theorem checked2827 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2827 (maskNeeds ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq2827]
  exact B2827.sound accepted2827
#print axioms checked2827

def Tip2764_2765 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2765 ![10384593717069655257060992658440577, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2765
def B2824 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 1496577682202030887873229054085403380289765300600848, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 1079).pointIds 1079), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq2824 : B2824.tree = HexagonCover.NBand.M6900_7100.SplitData.node2824 := by
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

def B2823 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2824, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 645).pointIds 645)]
theorem treeEq2823 : B2823.tree = HexagonCover.NBand.M6900_7100.SplitData.node2823 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2824
  · rfl
  · rfl

def B2822 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2823, (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq2822 : B2822.tree = HexagonCover.NBand.M6900_7100.SplitData.node2822 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2823
  · rfl

def B2821 : Block := .branch 166 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B2822, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2821 : B2821.tree = HexagonCover.NBand.M6900_7100.SplitData.node2821 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2822
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2820 : Block := .branch 91 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 6383839151883162018196952788146183449004930825191488] ![B2821, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 1078).pointIds 1078)]
theorem treeEq2820 : B2820.tree = HexagonCover.NBand.M6900_7100.SplitData.node2820 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2821
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2819 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713340288200494231129161792] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2820]
theorem treeEq2819 : B2819.tree = HexagonCover.NBand.M6900_7100.SplitData.node2819 := by
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
  · exact treeEq2820

def B2818 : Block := .branch 161 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713340288200494231129161792] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), B2819, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq2818 : B2818.tree = HexagonCover.NBand.M6900_7100.SplitData.node2818 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2819
  · rfl
  · rfl
  · rfl

def B2817 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2818]
theorem treeEq2817 : B2817.tree = HexagonCover.NBand.M6900_7100.SplitData.node2817 := by
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
  · exact treeEq2818

def B2816 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B2817, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1076).pointIds 1076)]
theorem treeEq2816 : B2816.tree = HexagonCover.NBand.M6900_7100.SplitData.node2816 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2817
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2815 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2816, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2815 : B2815.tree = HexagonCover.NBand.M6900_7100.SplitData.node2815 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2816
  · rfl

def B2814 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2815, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq2814 : B2814.tree = HexagonCover.NBand.M6900_7100.SplitData.node2814 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2815
  · rfl
  · rfl

def B2764 : Block := .branch 78 ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip2764_2765, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2814]
theorem treeEq2764 : B2764.tree = HexagonCover.NBand.M6900_7100.SplitData.node2764 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2814

theorem accepted2764 : B2764.accepted = true := by decide +kernel
theorem checked2764 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2764 (maskNeeds ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2764]
  exact B2764.sound accepted2764
#print axioms checked2764

def B2870 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6373608640421845697769209617137366223595704740741184] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1150).pointIds 1150), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1151).pointIds 1151)]
theorem treeEq2870 : B2870.tree = HexagonCover.NBand.M6900_7100.SplitData.node2870 := by
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

def B2869 : Block := .branch 160 ![385, 748288838313422294120286634350884480017526650045954, 18446884811197913092, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6372147138784514794851005932304649940576048808198208] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1149).pointIds 1149), (.leaf 2 (Common.fact 1138).pointIds 1138), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2870]
theorem treeEq2869 : B2869.tree = HexagonCover.NBand.M6900_7100.SplitData.node2869 := by
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
  · exact treeEq2870

def B2868 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B2869, (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq2868 : B2868.tree = HexagonCover.NBand.M6900_7100.SplitData.node2868 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2869
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2867 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2868]
theorem treeEq2867 : B2867.tree = HexagonCover.NBand.M6900_7100.SplitData.node2867 := by
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
  · exact treeEq2868

def B2866 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2867, (.leaf 0 [] 0)]
theorem treeEq2866 : B2866.tree = HexagonCover.NBand.M6900_7100.SplitData.node2866 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2867
  · rfl

def B2865 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2866, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2865 : B2865.tree = HexagonCover.NBand.M6900_7100.SplitData.node2865 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2866
  · rfl

def B2864 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2865, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq2864 : B2864.tree = HexagonCover.NBand.M6900_7100.SplitData.node2864 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2865
  · rfl
  · rfl

def B2863 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2864, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq2863 : B2863.tree = HexagonCover.NBand.M6900_7100.SplitData.node2863 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2864
  · rfl

def B2862 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2863, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2862 : B2862.tree = HexagonCover.NBand.M6900_7100.SplitData.node2862 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2863
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2861 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573953689188042242, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2862]
theorem treeEq2861 : B2861.tree = HexagonCover.NBand.M6900_7100.SplitData.node2861 := by
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
  · exact treeEq2862

def B2860 : Block := .branch 171 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2861, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2860 : B2860.tree = HexagonCover.NBand.M6900_7100.SplitData.node2860 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2861
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2859 : Block := .branch 151 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2860, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2859 : B2859.tree = HexagonCover.NBand.M6900_7100.SplitData.node2859 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2860
  · rfl

def B2858 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2859, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2858 : B2858.tree = HexagonCover.NBand.M6900_7100.SplitData.node2858 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2859
  · rfl
  · rfl

def B2857 : Block := .branch 172 ![385, 147718068877263898114, 18446884811197913092, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1092).pointIds 1092), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2858]
theorem treeEq2857 : B2857.tree = HexagonCover.NBand.M6900_7100.SplitData.node2857 := by
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
  · exact treeEq2858

theorem accepted2857 : B2857.accepted = true := by decide +kernel
theorem checked2857 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2857 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2857]
  exact B2857.sound accepted2857
#print axioms checked2857

def Tip2762_2827 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2827 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] checked2827
def Tip2762_2764 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2764 ![10384593717069655257060992658440577, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2764
def Tip2762_2857 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2857 ![385, 147718068877263898114, 18446884811197913092, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2857
def B2856 : Block := .branch 142 ![385, 1538, 6148, 24584, 2722258935367507707706996859454145789968, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq2856 : B2856.tree = HexagonCover.NBand.M6900_7100.SplitData.node2856 := by
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
  · rfl

def B2855 : Block := .branch 131 ![385, 1538, 6148, 24584, 98320, 393248, 6011156234363781774055012691349342955797321969303616] ![(.leaf 0 (Common.fact 512).pointIds 512), (.leaf 1 (Common.fact 513).pointIds 513), (.leaf 2 (Common.fact 514).pointIds 514), (.leaf 3 (Common.fact 515).pointIds 515), B2856, (.leaf 5 (Common.fact 517).pointIds 517), (.leaf 6 (Common.fact 1148).pointIds 1148)]
theorem treeEq2855 : B2855.tree = HexagonCover.NBand.M6900_7100.SplitData.node2855 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2856
  · rfl
  · rfl

def B2854 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 393248, 6011156234363781774055012691349342955797321969303616] ![(.leaf 0 (Common.fact 896).pointIds 896), (.leaf 1 (Common.fact 897).pointIds 897), (.leaf 2 (Common.fact 898).pointIds 898), (.leaf 3 (Common.fact 899).pointIds 899), (.leaf 4 (Common.fact 900).pointIds 900), B2855, (.leaf 6 (Common.fact 1147).pointIds 1147)]
theorem treeEq2854 : B2854.tree = HexagonCover.NBand.M6900_7100.SplitData.node2854 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2855
  · rfl

def B2853 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 24845527856403421092719616543447707286622273273920] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2854]
theorem treeEq2853 : B2853.tree = HexagonCover.NBand.M6900_7100.SplitData.node2853 := by
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
  · exact treeEq2854

def B2852 : Block := .branch 161 ![385, 144116287587485186, 18446884811197913092, 24584, 713623846352979940529142984724747568191471632, 393248, 24845527856403421092719616543447707286622273273920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), B2853, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1146).pointIds 1146)]
theorem treeEq2852 : B2852.tree = HexagonCover.NBand.M6900_7100.SplitData.node2852 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2853
  · rfl
  · rfl
  · rfl

def B2851 : Block := .branch 164 ![2993155353253689176481149013283026195015899646263681, 144116287587485186, 18446884811197913092, 24584, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 1060).pointIds 1060), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2852]
theorem treeEq2851 : B2851.tree = HexagonCover.NBand.M6900_7100.SplitData.node2851 := by
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
  · exact treeEq2852

def B2850 : Block := .branch 171 ![2475880078570760549798248833, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 1461501659108974401460659219987178972127352586304] ![B2851, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq2850 : B2850.tree = HexagonCover.NBand.M6900_7100.SplitData.node2850 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2851
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2849 : Block := .branch 151 ![2475880078570760549798248833, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2850, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2849 : B2849.tree = HexagonCover.NBand.M6900_7100.SplitData.node2849 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2850
  · rfl

def B2848 : Block := .branch 170 ![2475880078570760549798248833, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2849, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1089).pointIds 1089)]
theorem treeEq2848 : B2848.tree = HexagonCover.NBand.M6900_7100.SplitData.node2848 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2849
  · rfl
  · rfl

def B2847 : Block := .branch 160 ![2475880078570760549798248833, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1145).pointIds 1145), (.leaf 2 (Common.fact 1138).pointIds 1138), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2848]
theorem treeEq2847 : B2847.tree = HexagonCover.NBand.M6900_7100.SplitData.node2847 := by
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
  · exact treeEq2848

def B2826 : Block := .branch 69 ![10384596192949733827821542456689025, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip2762_2827, B2847, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq2826 : B2826.tree = HexagonCover.NBand.M6900_7100.SplitData.node2826 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2847
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2825 : Block := .branch 91 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B2826, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq2825 : B2825.tree = HexagonCover.NBand.M6900_7100.SplitData.node2825 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2826
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2763 : Block := .branch 76 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip2762_2764, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B2825]
theorem treeEq2763 : B2763.tree = HexagonCover.NBand.M6900_7100.SplitData.node2763 := by
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
  · exact treeEq2825

def B2762 : Block := .branch 74 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B2763, Tip2762_2857, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq2762 : B2762.tree = HexagonCover.NBand.M6900_7100.SplitData.node2762 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2763
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2762 : B2762.accepted = true := by decide +kernel
theorem checked2762 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2762 (maskNeeds ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2762]
  exact B2762.sound accepted2762
#print axioms checked2762

end HexagonCover.NBand.M6900_7100.SplitTree.Run0038
