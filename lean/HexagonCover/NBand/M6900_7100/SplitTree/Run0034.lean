import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0033
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0034
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B2536 : Block := .branch 161 ![385, 1538, 18518801667747485700, 5986310706507378352962293113491521476178833286651912, 98320, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), (.leaf 3 (Common.fact 1081).pointIds 1081), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1082).pointIds 1082)]
theorem treeEq2536 : B2536.tree = HexagonCover.NBand.M6900_7100.SplitData.node2536 := by
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

def B2535 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), B2536, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2535 : B2535.tree = HexagonCover.NBand.M6900_7100.SplitData.node2535 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2536
  · rfl
  · rfl
  · rfl

def B2534 : Block := .branch 124 ![10387129018874574625671300652204417, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 1080).pointIds 1080), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B2535]
theorem treeEq2534 : B2534.tree = HexagonCover.NBand.M6900_7100.SplitData.node2534 := by
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
  · exact treeEq2535

def B2544 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 1461501659108975050497766536840632538439393738816] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1087).pointIds 1087)]
theorem treeEq2544 : B2544.tree = HexagonCover.NBand.M6900_7100.SplitData.node2544 := by
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

def B2543 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2544, (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2543 : B2543.tree = HexagonCover.NBand.M6900_7100.SplitData.node2543 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2544
  · rfl
  · rfl

def B2542 : Block := .branch 132 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B2543]
theorem treeEq2542 : B2542.tree = HexagonCover.NBand.M6900_7100.SplitData.node2542 := by
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
  · exact treeEq2543

def B2541 : Block := .branch 86 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920826709157852111578770551805025777794678848] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B2542, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), (.leaf 6 (Common.fact 1086).pointIds 1086)]
theorem treeEq2541 : B2541.tree = HexagonCover.NBand.M6900_7100.SplitData.node2541 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2542
  · rfl
  · rfl
  · rfl

def B2540 : Block := .branch 133 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2541]
theorem treeEq2540 : B2540.tree = HexagonCover.NBand.M6900_7100.SplitData.node2540 := by
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
  · exact treeEq2541

def B2539 : Block := .branch 157 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2540, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2539 : B2539.tree = HexagonCover.NBand.M6900_7100.SplitData.node2539 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2540
  · rfl
  · rfl

def B2538 : Block := .branch 171 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2539, (.leaf 6 (Common.fact 1085).pointIds 1085)]
theorem treeEq2538 : B2538.tree = HexagonCover.NBand.M6900_7100.SplitData.node2538 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2539
  · rfl

def B2537 : Block := .branch 160 ![10384593717070245552871351364092289, 906694508967996956870146, 18518801667747485700, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1083).pointIds 1083), (.leaf 2 (Common.fact 1084).pointIds 1084), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2538]
theorem treeEq2537 : B2537.tree = HexagonCover.NBand.M6900_7100.SplitData.node2537 := by
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
  · exact treeEq2538

def B2533 : Block := .branch 79 ![10387129018270702011674344770503041, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B2534, B2537, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq2533 : B2533.tree = HexagonCover.NBand.M6900_7100.SplitData.node2533 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2534
  · exact treeEq2537
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2547 : Block := .branch 132 ![385, 1538, 6148, 24584, 184114952359068824656518890058984872593374412816, 393248, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq2547 : B2547.tree = HexagonCover.NBand.M6900_7100.SplitData.node2547 := by
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

def B2546 : Block := .branch 157 ![385, 1538, 6148, 24584, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2547, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2546 : B2546.tree = HexagonCover.NBand.M6900_7100.SplitData.node2546 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2547
  · rfl
  · rfl

def B2545 : Block := .branch 171 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2546, (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq2545 : B2545.tree = HexagonCover.NBand.M6900_7100.SplitData.node2545 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2546
  · rfl

def B2532 : Block := .branch 78 ![10387129018270702011674344770503041, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B2533, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2545]
theorem treeEq2532 : B2532.tree = HexagonCover.NBand.M6900_7100.SplitData.node2532 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2533
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2545

def B2531 : Block := .branch 101 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B2532, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq2531 : B2531.tree = HexagonCover.NBand.M6900_7100.SplitData.node2531 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2530 : Block := .branch 109 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2531]
theorem treeEq2530 : B2530.tree = HexagonCover.NBand.M6900_7100.SplitData.node2530 := by
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
  · exact treeEq2531

def B2529 : Block := .branch 150 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2530, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2529 : B2529.tree = HexagonCover.NBand.M6900_7100.SplitData.node2529 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2530
  · rfl
  · rfl

def B2528 : Block := .branch 125 ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B2529, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2528 : B2528.tree = HexagonCover.NBand.M6900_7100.SplitData.node2528 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2529
  · rfl

theorem accepted2528 : B2528.accepted = true := by decide +kernel
theorem checked2528 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2528 (maskNeeds ![10384593717070245552871351364092289, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq2528]
  exact B2528.sound accepted2528
#print axioms checked2528

def Tip2465_2466 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2466 ![10384593717069655257060992658440577, 302231599160682369517058, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0033.checked2466
def B2525 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 1496577682202030887873229054085403380289765300600848, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 1079).pointIds 1079), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq2525 : B2525.tree = HexagonCover.NBand.M6900_7100.SplitData.node2525 := by
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

def B2524 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2525, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 645).pointIds 645)]
theorem treeEq2524 : B2524.tree = HexagonCover.NBand.M6900_7100.SplitData.node2524 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2525
  · rfl
  · rfl

def B2523 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2524, (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq2523 : B2523.tree = HexagonCover.NBand.M6900_7100.SplitData.node2523 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2524
  · rfl

def B2522 : Block := .branch 166 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B2523, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2522 : B2522.tree = HexagonCover.NBand.M6900_7100.SplitData.node2522 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2523
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2521 : Block := .branch 91 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 6383839151883162018196952788146183449004930825191488] ![B2522, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 1078).pointIds 1078)]
theorem treeEq2521 : B2521.tree = HexagonCover.NBand.M6900_7100.SplitData.node2521 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2522
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2520 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 2923003274661805836407408351058793707445455708168, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713340288200494231129161792] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), (.leaf 3 (Common.fact 1066).pointIds 1066), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2521]
theorem treeEq2520 : B2520.tree = HexagonCover.NBand.M6900_7100.SplitData.node2520 := by
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
  · exact treeEq2521

def B2519 : Block := .branch 161 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 397528445375783665234659713340288200494231129161792] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1047).pointIds 1047), B2520, (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq2519 : B2519.tree = HexagonCover.NBand.M6900_7100.SplitData.node2519 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2520
  · rfl
  · rfl
  · rfl

def B2518 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2519]
theorem treeEq2518 : B2518.tree = HexagonCover.NBand.M6900_7100.SplitData.node2518 := by
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
  · exact treeEq2519

def B2517 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B2518, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1076).pointIds 1076)]
theorem treeEq2517 : B2517.tree = HexagonCover.NBand.M6900_7100.SplitData.node2517 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2518
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2516 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2517, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2516 : B2516.tree = HexagonCover.NBand.M6900_7100.SplitData.node2516 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2517
  · rfl

def B2515 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2516, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq2515 : B2515.tree = HexagonCover.NBand.M6900_7100.SplitData.node2515 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2516
  · rfl
  · rfl

def B2465 : Block := .branch 78 ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip2465_2466, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2515]
theorem treeEq2465 : B2465.tree = HexagonCover.NBand.M6900_7100.SplitData.node2465 := by
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
  · exact treeEq2515

theorem accepted2465 : B2465.accepted = true := by decide +kernel
theorem checked2465 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2465 (maskNeeds ![10384593717069655257060992658440577, 144257025075840514, 18518801667747485700, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2465]
  exact B2465.sound accepted2465
#print axioms checked2465

def B2567 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906205674461988354, 6148, 24584, 98320, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1099).pointIds 1099)]
theorem treeEq2567 : B2567.tree = HexagonCover.NBand.M6900_7100.SplitData.node2567 := by
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

def B2566 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B2567, (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq2566 : B2566.tree = HexagonCover.NBand.M6900_7100.SplitData.node2566 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2567
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2565 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2566]
theorem treeEq2565 : B2565.tree = HexagonCover.NBand.M6900_7100.SplitData.node2565 := by
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
  · exact treeEq2566

def B2564 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2565, (.leaf 0 [] 0)]
theorem treeEq2564 : B2564.tree = HexagonCover.NBand.M6900_7100.SplitData.node2564 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2565
  · rfl

def B2563 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2564, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2563 : B2563.tree = HexagonCover.NBand.M6900_7100.SplitData.node2563 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2564
  · rfl

def B2562 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2563, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq2562 : B2562.tree = HexagonCover.NBand.M6900_7100.SplitData.node2562 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2563
  · rfl
  · rfl

def B2561 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2562, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq2561 : B2561.tree = HexagonCover.NBand.M6900_7100.SplitData.node2561 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2562
  · rfl

def B2560 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2561, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2560 : B2560.tree = HexagonCover.NBand.M6900_7100.SplitData.node2560 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2561
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2559 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2560]
theorem treeEq2559 : B2559.tree = HexagonCover.NBand.M6900_7100.SplitData.node2559 := by
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
  · exact treeEq2560

def B2558 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2559, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2558 : B2558.tree = HexagonCover.NBand.M6900_7100.SplitData.node2558 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2559
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2557 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2558, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2557 : B2557.tree = HexagonCover.NBand.M6900_7100.SplitData.node2557 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2558
  · rfl

def B2556 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2557, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2556 : B2556.tree = HexagonCover.NBand.M6900_7100.SplitData.node2556 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2557
  · rfl
  · rfl

def B2555 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), (.leaf 3 (Common.fact 1092).pointIds 1092), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2556]
theorem treeEq2555 : B2555.tree = HexagonCover.NBand.M6900_7100.SplitData.node2555 := by
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
  · exact treeEq2556

theorem accepted2555 : B2555.accepted = true := by decide +kernel
theorem checked2555 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2555 (maskNeeds ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2555]
  exact B2555.sound accepted2555
#print axioms checked2555

def B2580 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906205674461988354, 6148, 24584, 98320, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1099).pointIds 1099)]
theorem treeEq2580 : B2580.tree = HexagonCover.NBand.M6900_7100.SplitData.node2580 := by
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

def B2579 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B2580, (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq2579 : B2579.tree = HexagonCover.NBand.M6900_7100.SplitData.node2579 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2580
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2578 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2579]
theorem treeEq2578 : B2578.tree = HexagonCover.NBand.M6900_7100.SplitData.node2578 := by
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
  · exact treeEq2579

def B2577 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2578, (.leaf 0 [] 0)]
theorem treeEq2577 : B2577.tree = HexagonCover.NBand.M6900_7100.SplitData.node2577 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2578
  · rfl

def B2576 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2577, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2576 : B2576.tree = HexagonCover.NBand.M6900_7100.SplitData.node2576 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2577
  · rfl

def B2575 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2576, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq2575 : B2575.tree = HexagonCover.NBand.M6900_7100.SplitData.node2575 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2576
  · rfl
  · rfl

def B2574 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2575, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq2574 : B2574.tree = HexagonCover.NBand.M6900_7100.SplitData.node2574 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2575
  · rfl

def B2573 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2574, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2573 : B2573.tree = HexagonCover.NBand.M6900_7100.SplitData.node2573 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2574
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2572 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2573]
theorem treeEq2572 : B2572.tree = HexagonCover.NBand.M6900_7100.SplitData.node2572 := by
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
  · exact treeEq2573

def B2571 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2572, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2571 : B2571.tree = HexagonCover.NBand.M6900_7100.SplitData.node2571 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2572
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2570 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2571, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2570 : B2570.tree = HexagonCover.NBand.M6900_7100.SplitData.node2570 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2571
  · rfl

def B2569 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2570, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2569 : B2569.tree = HexagonCover.NBand.M6900_7100.SplitData.node2569 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2570
  · rfl
  · rfl

def B2568 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2569]
theorem treeEq2568 : B2568.tree = HexagonCover.NBand.M6900_7100.SplitData.node2568 := by
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
  · exact treeEq2569

theorem accepted2568 : B2568.accepted = true := by decide +kernel
theorem checked2568 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2568 (maskNeeds ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2568]
  exact B2568.sound accepted2568
#print axioms checked2568

def B2593 : Block := .branch 69 ![2993155353253689176481146537402947624255349848015233, 748288838313422294120286634350736906205674461988354, 6148, 24584, 98320, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 1073).pointIds 1073), (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 1099).pointIds 1099)]
theorem treeEq2593 : B2593.tree = HexagonCover.NBand.M6900_7100.SplitData.node2593 := by
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

def B2592 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6372147138784514794851006241789659761921117532979264] ![(.leaf 0 (Common.fact 928).pointIds 928), B2593, (.leaf 2 (Common.fact 1050).pointIds 1050), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 1097).pointIds 1097)]
theorem treeEq2592 : B2592.tree = HexagonCover.NBand.M6900_7100.SplitData.node2592 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2593
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2591 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2592]
theorem treeEq2591 : B2591.tree = HexagonCover.NBand.M6900_7100.SplitData.node2591 := by
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
  · exact treeEq2592

def B2590 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2591, (.leaf 0 [] 0)]
theorem treeEq2590 : B2590.tree = HexagonCover.NBand.M6900_7100.SplitData.node2590 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2591
  · rfl

def B2589 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2590, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2589 : B2589.tree = HexagonCover.NBand.M6900_7100.SplitData.node2589 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2590
  · rfl

def B2588 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2589, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 1096).pointIds 1096)]
theorem treeEq2588 : B2588.tree = HexagonCover.NBand.M6900_7100.SplitData.node2588 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2589
  · rfl
  · rfl

def B2587 : Block := .branch 143 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505376763127929497763870072635456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B2588, (.leaf 6 (Common.fact 1095).pointIds 1095)]
theorem treeEq2587 : B2587.tree = HexagonCover.NBand.M6900_7100.SplitData.node2587 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2588
  · rfl

def B2586 : Block := .branch 166 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2587, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2586 : B2586.tree = HexagonCover.NBand.M6900_7100.SplitData.node2586 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2587
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2585 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 141836999984642, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2586]
theorem treeEq2585 : B2585.tree = HexagonCover.NBand.M6900_7100.SplitData.node2585 := by
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
  · exact treeEq2586

def B2584 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 6360455125685867571505693830520491465786778610827328] ![B2585, (.leaf 1 (Common.fact 1051).pointIds 1051), (.leaf 2 (Common.fact 1052).pointIds 1052), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2584 : B2584.tree = HexagonCover.NBand.M6900_7100.SplitData.node2584 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2585
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2583 : Block := .branch 151 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2584, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2583 : B2583.tree = HexagonCover.NBand.M6900_7100.SplitData.node2583 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2584
  · rfl

def B2582 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1055).pointIds 1055), (.leaf 2 (Common.fact 1056).pointIds 1056), (.leaf 3 (Common.fact 658).pointIds 658), B2583, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2582 : B2582.tree = HexagonCover.NBand.M6900_7100.SplitData.node2582 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2583
  · rfl
  · rfl

def B2581 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1044).pointIds 1044), (.leaf 2 (Common.fact 1045).pointIds 1045), (.leaf 3 (Common.fact 1101).pointIds 1101), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2582]
theorem treeEq2581 : B2581.tree = HexagonCover.NBand.M6900_7100.SplitData.node2581 := by
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
  · exact treeEq2582

theorem accepted2581 : B2581.accepted = true := by decide +kernel
theorem checked2581 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2581 (maskNeeds ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2581]
  exact B2581.sound accepted2581
#print axioms checked2581

end HexagonCover.NBand.M6900_7100.SplitTree.Run0034
