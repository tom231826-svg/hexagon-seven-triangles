import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0045
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0046
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3388_3390 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3390 ![10384593717069655257060992658440577, 618970019786805325525419522, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0045.checked3390
def Tip3388_3426 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3426 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] HexagonCover.NBand.M6900_7100.SplitTree.Run0045.checked3426
def B3425 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 5444517870735015415413993718908291481616, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1069).pointIds 1069), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1070).pointIds 1070)]
theorem treeEq3425 : B3425.tree = HexagonCover.NBand.M6900_7100.SplitData.node3425 := by
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

def B3424 : Block := .branch 132 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), B3425, (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1068).pointIds 1068)]
theorem treeEq3424 : B3424.tree = HexagonCover.NBand.M6900_7100.SplitData.node3424 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3425
  · rfl
  · rfl

def B3423 : Block := .branch 143 ![385, 1538, 6148, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 6383839151883162018196636029936399847423433718104128] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3424, (.leaf 6 (Common.fact 1067).pointIds 1067)]
theorem treeEq3423 : B3423.tree = HexagonCover.NBand.M6900_7100.SplitData.node3423 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3424
  · rfl

def B3422 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 2923003274661805836486597827946830376905409060872, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234342955130504598912734022074432] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3423]
theorem treeEq3422 : B3422.tree = HexagonCover.NBand.M6900_7100.SplitData.node3422 := by
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
  · exact treeEq3423

def B3421 : Block := .branch 161 ![385, 144115188075857410, 18446745173221185540, 79228162514264337593543974920, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234660022523066566935642560266304] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), B3422, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1065).pointIds 1065)]
theorem treeEq3421 : B3421.tree = HexagonCover.NBand.M6900_7100.SplitData.node3421 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3422
  · rfl
  · rfl
  · rfl

def B3420 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 79228162514264337593543974920, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401065199606038621147639578688] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3421]
theorem treeEq3420 : B3420.tree = HexagonCover.NBand.M6900_7100.SplitData.node3420 := by
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
  · exact treeEq3421

def B3419 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401065199606038621147639578688] ![B3420, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq3419 : B3419.tree = HexagonCover.NBand.M6900_7100.SplitData.node3419 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3420
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3418 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3419, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3418 : B3418.tree = HexagonCover.NBand.M6900_7100.SplitData.node3418 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3419
  · rfl

def B3417 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3418, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq3417 : B3417.tree = HexagonCover.NBand.M6900_7100.SplitData.node3417 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3418
  · rfl
  · rfl

def B3389 : Block := .branch 89 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip3388_3390, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B3417]
theorem treeEq3389 : B3389.tree = HexagonCover.NBand.M6900_7100.SplitData.node3389 := by
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
  · exact treeEq3417

def B3388 : Block := .branch 86 ![10384593717069655257060992658440577, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B3389, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), Tip3388_3426]
theorem treeEq3388 : B3388.tree = HexagonCover.NBand.M6900_7100.SplitData.node3388 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3389
  · rfl
  · rfl
  · rfl

theorem accepted3388 : B3388.accepted = true := by decide +kernel
theorem checked3388 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3388 (maskNeeds ![10384593717069655257060992658440577, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3388]
  exact B3388.sound accepted3388
#print axioms checked3388

def B3458 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293113491521476178833286651912, 98320, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1081).pointIds 1081), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1082).pointIds 1082)]
theorem treeEq3458 : B3458.tree = HexagonCover.NBand.M6900_7100.SplitData.node3458 := by
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

def B3457 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B3458, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq3457 : B3457.tree = HexagonCover.NBand.M6900_7100.SplitData.node3457 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3458
  · rfl
  · rfl
  · rfl

def B3456 : Block := .branch 124 ![10387129018874574625671300652204417, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 1080).pointIds 1080), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B3457]
theorem treeEq3456 : B3456.tree = HexagonCover.NBand.M6900_7100.SplitData.node3456 := by
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
  · exact treeEq3457

def B3466 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 1461501659108975050497766536840632538439393738816] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1087).pointIds 1087)]
theorem treeEq3466 : B3466.tree = HexagonCover.NBand.M6900_7100.SplitData.node3466 := by
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

def B3465 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B3466, (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3465 : B3465.tree = HexagonCover.NBand.M6900_7100.SplitData.node3465 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3466
  · rfl
  · rfl

def B3464 : Block := .branch 132 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B3465]
theorem treeEq3464 : B3464.tree = HexagonCover.NBand.M6900_7100.SplitData.node3464 := by
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
  · exact treeEq3465

def B3463 : Block := .branch 86 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920826709157852111578770551805025777794678848] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B3464, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), (.leaf 6 (Common.fact 1086).pointIds 1086)]
theorem treeEq3463 : B3463.tree = HexagonCover.NBand.M6900_7100.SplitData.node3463 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3464
  · rfl
  · rfl
  · rfl

def B3462 : Block := .branch 133 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B3463]
theorem treeEq3462 : B3462.tree = HexagonCover.NBand.M6900_7100.SplitData.node3462 := by
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
  · exact treeEq3463

def B3461 : Block := .branch 157 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B3462, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq3461 : B3461.tree = HexagonCover.NBand.M6900_7100.SplitData.node3461 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3462
  · rfl
  · rfl

def B3460 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B3461, (.leaf 6 (Common.fact 1085).pointIds 1085)]
theorem treeEq3460 : B3460.tree = HexagonCover.NBand.M6900_7100.SplitData.node3460 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3461
  · rfl

def B3459 : Block := .branch 160 ![10384593717070245552871351364092289, 906694508826159956887042, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1194).pointIds 1194), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B3460]
theorem treeEq3459 : B3459.tree = HexagonCover.NBand.M6900_7100.SplitData.node3459 := by
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
  · exact treeEq3460

def B3455 : Block := .branch 79 ![10387129018270702011674344770503041, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B3456, B3459, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq3455 : B3455.tree = HexagonCover.NBand.M6900_7100.SplitData.node3455 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3456
  · exact treeEq3459
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3469 : Block := .branch 132 ![385, 1538, 6148, 24584, 184114952359068824656518890058984872593374412816, 393248, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq3469 : B3469.tree = HexagonCover.NBand.M6900_7100.SplitData.node3469 := by
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

def B3468 : Block := .branch 157 ![385, 1538, 6148, 24584, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B3469, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq3468 : B3468.tree = HexagonCover.NBand.M6900_7100.SplitData.node3468 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3469
  · rfl
  · rfl

def B3467 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B3468, (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3467 : B3467.tree = HexagonCover.NBand.M6900_7100.SplitData.node3467 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3468
  · rfl

def B3454 : Block := .branch 78 ![10387129018270702011674344770503041, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B3455, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B3467]
theorem treeEq3454 : B3454.tree = HexagonCover.NBand.M6900_7100.SplitData.node3454 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3455
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3467

def B3453 : Block := .branch 101 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B3454, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq3453 : B3453.tree = HexagonCover.NBand.M6900_7100.SplitData.node3453 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3454
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3452 : Block := .branch 109 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B3453]
theorem treeEq3452 : B3452.tree = HexagonCover.NBand.M6900_7100.SplitData.node3452 := by
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
  · exact treeEq3453

def B3451 : Block := .branch 150 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B3452, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq3451 : B3451.tree = HexagonCover.NBand.M6900_7100.SplitData.node3451 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3452
  · rfl
  · rfl

def B3450 : Block := .branch 125 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B3451, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq3450 : B3450.tree = HexagonCover.NBand.M6900_7100.SplitData.node3450 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3451
  · rfl

theorem accepted3450 : B3450.accepted = true := by decide +kernel
theorem checked3450 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3450 (maskNeeds ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq3450]
  exact B3450.sound accepted3450
#print axioms checked3450

def Tip3387_3388 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3388 ![10384593717069655257060992658440577, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3388
def B3447 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 1496577682202030887873229054085403380289765300600848, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 1079).pointIds 1079), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq3447 : B3447.tree = HexagonCover.NBand.M6900_7100.SplitData.node3447 := by
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

def B3446 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B3447, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 645).pointIds 645)]
theorem treeEq3446 : B3446.tree = HexagonCover.NBand.M6900_7100.SplitData.node3446 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3447
  · rfl
  · rfl

def B3445 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3446, (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq3445 : B3445.tree = HexagonCover.NBand.M6900_7100.SplitData.node3445 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3446
  · rfl

def B3444 : Block := .branch 166 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B3445, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3444 : B3444.tree = HexagonCover.NBand.M6900_7100.SplitData.node3444 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3445
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3443 : Block := .branch 91 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 6383839151883162018196952788146183449004930825191488] ![B3444, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 1078).pointIds 1078)]
theorem treeEq3443 : B3443.tree = HexagonCover.NBand.M6900_7100.SplitData.node3443 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3444
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3442 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713340288200494231129161792] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3443]
theorem treeEq3442 : B3442.tree = HexagonCover.NBand.M6900_7100.SplitData.node3442 := by
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
  · exact treeEq3443

def B3441 : Block := .branch 161 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713340288200494231129161792] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), B3442, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq3441 : B3441.tree = HexagonCover.NBand.M6900_7100.SplitData.node3441 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3442
  · rfl
  · rfl
  · rfl

def B3440 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3441]
theorem treeEq3440 : B3440.tree = HexagonCover.NBand.M6900_7100.SplitData.node3440 := by
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
  · exact treeEq3441

def B3439 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B3440, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1076).pointIds 1076)]
theorem treeEq3439 : B3439.tree = HexagonCover.NBand.M6900_7100.SplitData.node3439 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3440
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3438 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3439, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3438 : B3438.tree = HexagonCover.NBand.M6900_7100.SplitData.node3438 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3439
  · rfl

def B3437 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3438, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq3437 : B3437.tree = HexagonCover.NBand.M6900_7100.SplitData.node3437 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3438
  · rfl
  · rfl

def B3387 : Block := .branch 78 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip3387_3388, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B3437]
theorem treeEq3387 : B3387.tree = HexagonCover.NBand.M6900_7100.SplitData.node3387 := by
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
  · exact treeEq3437

theorem accepted3387 : B3387.accepted = true := by decide +kernel
theorem checked3387 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3387 (maskNeeds ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3387]
  exact B3387.sound accepted3387
#print axioms checked3387

def B3493 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6373608640421845697769209617137366223595704740741184] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 1150).pointIds 1150), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 1151).pointIds 1151)]
theorem treeEq3493 : B3493.tree = HexagonCover.NBand.M6900_7100.SplitData.node3493 := by
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

def B3492 : Block := .branch 160 ![385, 748288838313422294120286634350884480016427138418178, 18446745173221185540, 79228162514264337593543974920, 1496577682202030887873229054085403380289765300600848, 393248, 6372147138784514794851005932304649940576048808198208] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1196).pointIds 1196), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B3493]
theorem treeEq3492 : B3492.tree = HexagonCover.NBand.M6900_7100.SplitData.node3492 := by
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
  · exact treeEq3493

def B3491 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B3492, (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq3491 : B3491.tree = HexagonCover.NBand.M6900_7100.SplitData.node3491 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3492
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3490 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B3491]
theorem treeEq3490 : B3490.tree = HexagonCover.NBand.M6900_7100.SplitData.node3490 := by
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
  · exact treeEq3491

def B3489 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B3490, (.leaf 0 [] 0)]
theorem treeEq3489 : B3489.tree = HexagonCover.NBand.M6900_7100.SplitData.node3489 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3490
  · rfl

def B3488 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B3489, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3488 : B3488.tree = HexagonCover.NBand.M6900_7100.SplitData.node3488 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3489
  · rfl

def B3487 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B3488, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq3487 : B3487.tree = HexagonCover.NBand.M6900_7100.SplitData.node3487 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3488
  · rfl
  · rfl

def B3486 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B3487, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq3486 : B3486.tree = HexagonCover.NBand.M6900_7100.SplitData.node3486 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3487
  · rfl

def B3485 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3486, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq3485 : B3485.tree = HexagonCover.NBand.M6900_7100.SplitData.node3485 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3486
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3484 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 147573952589676414466, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3485]
theorem treeEq3484 : B3484.tree = HexagonCover.NBand.M6900_7100.SplitData.node3484 := by
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
  · exact treeEq3485

def B3483 : Block := .branch 171 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B3484, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq3483 : B3483.tree = HexagonCover.NBand.M6900_7100.SplitData.node3483 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3484
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3482 : Block := .branch 151 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3483, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3482 : B3482.tree = HexagonCover.NBand.M6900_7100.SplitData.node3482 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3483
  · rfl

def B3481 : Block := .branch 170 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3482, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq3481 : B3481.tree = HexagonCover.NBand.M6900_7100.SplitData.node3481 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3482
  · rfl
  · rfl

def B3480 : Block := .branch 172 ![385, 147718067777752270338, 18446745173221185540, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1092).pointIds 1092), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3481]
theorem treeEq3480 : B3480.tree = HexagonCover.NBand.M6900_7100.SplitData.node3480 := by
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
  · exact treeEq3481

theorem accepted3480 : B3480.accepted = true := by decide +kernel
theorem checked3480 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3480 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3480]
  exact B3480.sound accepted3480
#print axioms checked3480

def Tip3385_3450 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3450 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] checked3450
def Tip3385_3387 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3387 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3387
def Tip3385_3480 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node3480 ![385, 147718067777752270338, 18446745173221185540, 79266867029957937205715427336, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked3480
def B3479 : Block := .branch 142 ![385, 1538, 6148, 24584, 2722258935367507707706996859454145789968, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq3479 : B3479.tree = HexagonCover.NBand.M6900_7100.SplitData.node3479 := by
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

def B3478 : Block := .branch 131 ![385, 1538, 6148, 24584, 98320, 393248, 6011156234363781774055012691349342955797321969303616] ![(.leaf 0 (Common.fact 512).pointIds 512), (.leaf 1 (Common.fact 513).pointIds 513), (.leaf 2 (Common.fact 514).pointIds 514), (.leaf 3 (Common.fact 515).pointIds 515), B3479, (.leaf 5 (Common.fact 517).pointIds 517), (.leaf 6 (Common.fact 1148).pointIds 1148)]
theorem treeEq3478 : B3478.tree = HexagonCover.NBand.M6900_7100.SplitData.node3478 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3479
  · rfl
  · rfl

def B3477 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 393248, 6011156234363781774055012691349342955797321969303616] ![(.leaf 0 (Common.fact 896).pointIds 896), (.leaf 1 (Common.fact 897).pointIds 897), (.leaf 2 (Common.fact 898).pointIds 898), (.leaf 3 (Common.fact 899).pointIds 899), (.leaf 4 (Common.fact 900).pointIds 900), B3478, (.leaf 6 (Common.fact 1147).pointIds 1147)]
theorem treeEq3477 : B3477.tree = HexagonCover.NBand.M6900_7100.SplitData.node3477 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3478
  · rfl

def B3476 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 24845527856403421092719616543447707286622273273920] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B3477]
theorem treeEq3476 : B3476.tree = HexagonCover.NBand.M6900_7100.SplitData.node3476 := by
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
  · exact treeEq3477

def B3475 : Block := .branch 161 ![385, 144115188075857410, 18446745173221185540, 24584, 713623846352979940529142984724747568191471632, 393248, 24845527856403421092719616543447707286622273273920] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), B3476, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1146).pointIds 1146)]
theorem treeEq3475 : B3475.tree = HexagonCover.NBand.M6900_7100.SplitData.node3475 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3476
  · rfl
  · rfl
  · rfl

def B3474 : Block := .branch 164 ![2993155353253689176481149013283026195015899646263681, 144115188075857410, 18446745173221185540, 24584, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 1060).pointIds 1060), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B3475]
theorem treeEq3474 : B3474.tree = HexagonCover.NBand.M6900_7100.SplitData.node3474 := by
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
  · exact treeEq3475

def B3473 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 1461501659108974401460659219987178972127352586304] ![B3474, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq3473 : B3473.tree = HexagonCover.NBand.M6900_7100.SplitData.node3473 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3474
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3472 : Block := .branch 151 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3473, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3472 : B3472.tree = HexagonCover.NBand.M6900_7100.SplitData.node3472 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3473
  · rfl

def B3471 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3472, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1089).pointIds 1089)]
theorem treeEq3471 : B3471.tree = HexagonCover.NBand.M6900_7100.SplitData.node3471 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3472
  · rfl
  · rfl

def B3470 : Block := .branch 160 ![2475880078570760549798248833, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1195).pointIds 1195), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B3471]
theorem treeEq3470 : B3470.tree = HexagonCover.NBand.M6900_7100.SplitData.node3470 := by
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
  · exact treeEq3471

def B3449 : Block := .branch 69 ![10384596192949733827821542456689025, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip3385_3450, B3470, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq3449 : B3449.tree = HexagonCover.NBand.M6900_7100.SplitData.node3449 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3470
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3448 : Block := .branch 91 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B3449, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq3448 : B3448.tree = HexagonCover.NBand.M6900_7100.SplitData.node3448 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3449
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3386 : Block := .branch 76 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip3385_3387, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B3448]
theorem treeEq3386 : B3386.tree = HexagonCover.NBand.M6900_7100.SplitData.node3386 := by
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
  · exact treeEq3448

def B3385 : Block := .branch 74 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B3386, Tip3385_3480, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq3385 : B3385.tree = HexagonCover.NBand.M6900_7100.SplitData.node3385 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3386
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3385 : B3385.accepted = true := by decide +kernel
theorem checked3385 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3385 (maskNeeds ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq3385]
  exact B3385.sound accepted3385
#print axioms checked3385

end HexagonCover.NBand.M6900_7100.SplitTree.Run0046
