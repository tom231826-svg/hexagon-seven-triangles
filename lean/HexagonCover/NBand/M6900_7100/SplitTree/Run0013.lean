import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0012
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0013
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1077 : Block := .branch 124 ![94266855607843238224137671710200254767807649022337, 1538, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1077 : B1077.tree = HexagonCover.NBand.M6900_7100.SplitData.node1077 := by
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
  · rfl

def B1076 : Block := .branch 159 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![B1077, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq1076 : B1076.tree = HexagonCover.NBand.M6900_7100.SplitData.node1076 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1077
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1075 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B1076, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq1075 : B1075.tree = HexagonCover.NBand.M6900_7100.SplitData.node1075 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1076
  · rfl
  · rfl
  · rfl
  · rfl

def B1074 : Block := .branch 161 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38695070960633872881049608, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1075, (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1074 : B1074.tree = HexagonCover.NBand.M6900_7100.SplitData.node1074 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1075
  · rfl
  · rfl
  · rfl
  · rfl

def B1073 : Block := .branch 137 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38695070960633872881049608, 5847433797016317632695797616834581573760113016848, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1074, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1073 : B1073.tree = HexagonCover.NBand.M6900_7100.SplitData.node1073 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1074
  · rfl
  · rfl
  · rfl

def B1072 : Block := .branch 162 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B1073, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq1072 : B1072.tree = HexagonCover.NBand.M6900_7100.SplitData.node1072 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1073
  · rfl
  · rfl

def B1071 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38695070960633872881049608, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 482).pointIds 482), B1072]
theorem treeEq1071 : B1071.tree = HexagonCover.NBand.M6900_7100.SplitData.node1071 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1072

def B1070 : Block := .branch 150 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38695070960633872881049608, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1071, (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1070 : B1070.tree = HexagonCover.NBand.M6900_7100.SplitData.node1070 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1071
  · rfl
  · rfl

def B1069 : Block := .branch 125 ![841824943102600080887857764845035478124810551165313, 737941821641931621890, 6148, 38695070960633872881049608, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1070, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1069 : B1069.tree = HexagonCover.NBand.M6900_7100.SplitData.node1069 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1070
  · rfl

def B1068 : Block := .branch 169 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![B1069, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 687).pointIds 687)]
theorem treeEq1068 : B1068.tree = HexagonCover.NBand.M6900_7100.SplitData.node1068 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1069
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1067 : Block := .branch 142 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B1068]
theorem treeEq1067 : B1067.tree = HexagonCover.NBand.M6900_7100.SplitData.node1067 := by
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
  · exact treeEq1068

def B1066 : Block := .branch 166 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755790154081001993238216768] ![B1067, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1066 : B1066.tree = HexagonCover.NBand.M6900_7100.SplitData.node1066 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1067
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1065 : Block := .branch 151 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B1066, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1065 : B1065.tree = HexagonCover.NBand.M6900_7100.SplitData.node1065 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1066
  · rfl

theorem accepted1065 : B1065.accepted = true := by decide +kernel
theorem checked1065 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1065 (maskNeeds ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1065]
  exact B1065.sound accepted1065
#print axioms checked1065

def Tip1063_1089 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1089 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] HexagonCover.NBand.M6900_7100.SplitTree.Run0012.checked1089
def Tip1063_1065 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1065 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] checked1065
def B1084 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1084 : B1084.tree = HexagonCover.NBand.M6900_7100.SplitData.node1084 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1083 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1084, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1083 : B1083.tree = HexagonCover.NBand.M6900_7100.SplitData.node1083 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1084
  · rfl
  · rfl

def B1082 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1083]
theorem treeEq1082 : B1082.tree = HexagonCover.NBand.M6900_7100.SplitData.node1082 := by
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
  · exact treeEq1083

def B1088 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1088 : B1088.tree = HexagonCover.NBand.M6900_7100.SplitData.node1088 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1087 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1088, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1087 : B1087.tree = HexagonCover.NBand.M6900_7100.SplitData.node1087 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1088
  · rfl
  · rfl

def B1086 : Block := .branch 124 ![10384594955009694542441267557564801, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1087]
theorem treeEq1086 : B1086.tree = HexagonCover.NBand.M6900_7100.SplitData.node1086 := by
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
  · exact treeEq1087

def B1085 : Block := .branch 90 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1086, Tip1063_1089, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1085 : B1085.tree = HexagonCover.NBand.M6900_7100.SplitData.node1085 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1086
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1081 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1082, B1085, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq1081 : B1081.tree = HexagonCover.NBand.M6900_7100.SplitData.node1081 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1082
  · exact treeEq1085
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1080 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1081, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1080 : B1080.tree = HexagonCover.NBand.M6900_7100.SplitData.node1080 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1081
  · rfl
  · rfl

def B1079 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1080, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1079 : B1079.tree = HexagonCover.NBand.M6900_7100.SplitData.node1079 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1080
  · rfl

def B1078 : Block := .branch 169 ![10387129018270111715863986064851329, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309448580807785149258793024] ![B1079, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq1078 : B1078.tree = HexagonCover.NBand.M6900_7100.SplitData.node1078 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1079
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1064 : Block := .branch 108 ![10387129018270111715863986064851329, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), Tip1063_1065, (.leaf 5 (Common.fact 322).pointIds 322), B1078]
theorem treeEq1064 : B1064.tree = HexagonCover.NBand.M6900_7100.SplitData.node1064 := by
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
  · exact treeEq1078

def B1113 : Block := .branch 164 ![93536104789220322060903422481853605844458452025729, 1538, 6148, 24584, 98320, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq1113 : B1113.tree = HexagonCover.NBand.M6900_7100.SplitData.node1113 := by
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

def B1112 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 98320, 2865645758011185073687339798035314453518876704, 21778071485792739815242086773067913625664] ![B1113, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1112 : B1112.tree = HexagonCover.NBand.M6900_7100.SplitData.node1112 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1113
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1111 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1112, (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq1111 : B1111.tree = HexagonCover.NBand.M6900_7100.SplitData.node1111 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1112
  · rfl

def B1110 : Block := .branch 166 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218545936056990610539804986644627520] ![B1111, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1110 : B1110.tree = HexagonCover.NBand.M6900_7100.SplitData.node1110 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1111
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1109 : Block := .branch 151 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1110, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1109 : B1109.tree = HexagonCover.NBand.M6900_7100.SplitData.node1109 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1110
  · rfl

def B1108 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1109, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq1108 : B1108.tree = HexagonCover.NBand.M6900_7100.SplitData.node1108 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1109
  · rfl
  · rfl

def B1063 : Block := .branch 101 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B1064, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B1108]
theorem treeEq1063 : B1063.tree = HexagonCover.NBand.M6900_7100.SplitData.node1063 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1064
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1108

theorem accepted1063 : B1063.accepted = true := by decide +kernel
theorem checked1063 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1063 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1063]
  exact B1063.sound accepted1063
#print axioms checked1063

def Tip1061_1063 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1063 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] checked1063
def B1121 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq1121 : B1121.tree = HexagonCover.NBand.M6900_7100.SplitData.node1121 := by
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

def B1120 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1121, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq1120 : B1120.tree = HexagonCover.NBand.M6900_7100.SplitData.node1120 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1121
  · rfl
  · rfl

def B1119 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1120]
theorem treeEq1119 : B1119.tree = HexagonCover.NBand.M6900_7100.SplitData.node1119 := by
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
  · exact treeEq1120

def B1118 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438614785627970074507214912] ![B1119, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1118 : B1118.tree = HexagonCover.NBand.M6900_7100.SplitData.node1118 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1119
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1117 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1118, (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq1117 : B1117.tree = HexagonCover.NBand.M6900_7100.SplitData.node1117 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1118
  · rfl

def B1116 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374760173723692130687778880] ![B1117, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1116 : B1116.tree = HexagonCover.NBand.M6900_7100.SplitData.node1116 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1117
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1115 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1116, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1115 : B1115.tree = HexagonCover.NBand.M6900_7100.SplitData.node1115 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1116
  · rfl

def B1114 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1115, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq1114 : B1114.tree = HexagonCover.NBand.M6900_7100.SplitData.node1114 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1115
  · rfl
  · rfl

def B1062 : Block := .branch 89 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip1061_1063, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B1114]
theorem treeEq1062 : B1062.tree = HexagonCover.NBand.M6900_7100.SplitData.node1062 := by
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
  · exact treeEq1114

def B1129 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq1129 : B1129.tree = HexagonCover.NBand.M6900_7100.SplitData.node1129 := by
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

def B1128 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1129, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq1128 : B1128.tree = HexagonCover.NBand.M6900_7100.SplitData.node1128 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1129
  · rfl
  · rfl

def B1127 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1128]
theorem treeEq1127 : B1127.tree = HexagonCover.NBand.M6900_7100.SplitData.node1127 := by
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
  · exact treeEq1128

def B1126 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257515986038083306341688410176] ![B1127, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1126 : B1126.tree = HexagonCover.NBand.M6900_7100.SplitData.node1126 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1127
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1125 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1126, (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1125 : B1125.tree = HexagonCover.NBand.M6900_7100.SplitData.node1125 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1126
  · rfl

def B1124 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833161406536338260419412032] ![B1125, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1124 : B1124.tree = HexagonCover.NBand.M6900_7100.SplitData.node1124 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1125
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1123 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1124, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1123 : B1123.tree = HexagonCover.NBand.M6900_7100.SplitData.node1123 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1124
  · rfl

def B1122 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1123, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq1122 : B1122.tree = HexagonCover.NBand.M6900_7100.SplitData.node1122 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1123
  · rfl
  · rfl

def B1061 : Block := .branch 86 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B1062, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B1122]
theorem treeEq1061 : B1061.tree = HexagonCover.NBand.M6900_7100.SplitData.node1061 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1062
  · rfl
  · rfl
  · exact treeEq1122

theorem accepted1061 : B1061.accepted = true := by decide +kernel
theorem checked1061 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1061 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1061]
  exact B1061.sound accepted1061
#print axioms checked1061

def Tip1009_1019 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1019 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] HexagonCover.NBand.M6900_7100.SplitTree.Run0012.checked1019
def B1018 : Block := .branch 142 ![385, 1538, 6148, 24584, 5847433797016317632695797616834581573760113016848, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq1018 : B1018.tree = HexagonCover.NBand.M6900_7100.SplitData.node1018 := by
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

def B1017 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B1018, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq1017 : B1017.tree = HexagonCover.NBand.M6900_7100.SplitData.node1017 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1018
  · rfl
  · rfl

def B1016 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 1538, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1017]
theorem treeEq1016 : B1016.tree = HexagonCover.NBand.M6900_7100.SplitData.node1016 := by
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
  · exact treeEq1017

def B1015 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 302674248820119872472578, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1016, Tip1009_1019, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq1015 : B1015.tree = HexagonCover.NBand.M6900_7100.SplitData.node1015 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1016
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1059 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1059 : B1059.tree = HexagonCover.NBand.M6900_7100.SplitData.node1059 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1058 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1059, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1058 : B1058.tree = HexagonCover.NBand.M6900_7100.SplitData.node1058 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1059
  · rfl
  · rfl

def B1014 : Block := .branch 78 ![748288838313422304507415652621438917738182232506753, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B1015, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1058]
theorem treeEq1014 : B1014.tree = HexagonCover.NBand.M6900_7100.SplitData.node1014 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1015
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1058

def B1013 : Block := .branch 101 ![748288838313422304504880351420982458935188826096001, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1014, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq1013 : B1013.tree = HexagonCover.NBand.M6900_7100.SplitData.node1013 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1014
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1012 : Block := .branch 169 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1013, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1012 : B1012.tree = HexagonCover.NBand.M6900_7100.SplitData.node1012 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1013
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1011 : Block := .branch 109 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1012]
theorem treeEq1011 : B1011.tree = HexagonCover.NBand.M6900_7100.SplitData.node1011 := by
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
  · exact treeEq1012

def B1010 : Block := .branch 150 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1011, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1010 : B1010.tree = HexagonCover.NBand.M6900_7100.SplitData.node1010 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1011
  · rfl
  · rfl

def B1009 : Block := .branch 125 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1010, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1009 : B1009.tree = HexagonCover.NBand.M6900_7100.SplitData.node1009 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1010
  · rfl

theorem accepted1009 : B1009.accepted = true := by decide +kernel
theorem checked1009 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1009 (maskNeeds ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1009]
  exact B1009.sound accepted1009
#print axioms checked1009

end HexagonCover.NBand.M6900_7100.SplitTree.Run0013
