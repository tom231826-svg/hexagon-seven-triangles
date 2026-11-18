import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0019
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0020
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1573 : Block := .branch 124 ![94266855607843238224137671710200254767807649022337, 1538, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1573 : B1573.tree = HexagonCover.NBand.M6900_7100.SplitData.node1573 := by
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

def B1572 : Block := .branch 159 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![B1573, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq1572 : B1572.tree = HexagonCover.NBand.M6900_7100.SplitData.node1572 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1573
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1571 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B1572, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq1571 : B1571.tree = HexagonCover.NBand.M6900_7100.SplitData.node1571 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1572
  · rfl
  · rfl
  · rfl
  · rfl

def B1570 : Block := .branch 161 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38690348594151003235835912, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1571, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1570 : B1570.tree = HexagonCover.NBand.M6900_7100.SplitData.node1570 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1571
  · rfl
  · rfl
  · rfl
  · rfl

def B1569 : Block := .branch 137 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1570, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1569 : B1569.tree = HexagonCover.NBand.M6900_7100.SplitData.node1569 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1570
  · rfl
  · rfl
  · rfl

def B1568 : Block := .branch 162 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1569, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq1568 : B1568.tree = HexagonCover.NBand.M6900_7100.SplitData.node1568 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1569
  · rfl
  · rfl

def B1567 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38690348594151003235835912, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 482).pointIds 482), B1568]
theorem treeEq1567 : B1567.tree = HexagonCover.NBand.M6900_7100.SplitData.node1567 := by
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
  · exact treeEq1568

def B1566 : Block := .branch 150 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 38690348594151003235835912, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1567, (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1566 : B1566.tree = HexagonCover.NBand.M6900_7100.SplitData.node1566 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1567
  · rfl
  · rfl

def B1565 : Block := .branch 125 ![841824943102600080887857764845035478124810551165313, 737941821641931621890, 6148, 38690348594151003235835912, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1566, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1565 : B1565.tree = HexagonCover.NBand.M6900_7100.SplitData.node1565 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1566
  · rfl

def B1564 : Block := .branch 169 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![B1565, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 687).pointIds 687)]
theorem treeEq1564 : B1564.tree = HexagonCover.NBand.M6900_7100.SplitData.node1564 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1565
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1563 : Block := .branch 142 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B1564]
theorem treeEq1563 : B1563.tree = HexagonCover.NBand.M6900_7100.SplitData.node1563 := by
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
  · exact treeEq1564

def B1562 : Block := .branch 166 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755790154081001993238216768] ![B1563, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1562 : B1562.tree = HexagonCover.NBand.M6900_7100.SplitData.node1562 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1563
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1561 : Block := .branch 151 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B1562, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1561 : B1561.tree = HexagonCover.NBand.M6900_7100.SplitData.node1561 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1562
  · rfl

theorem accepted1561 : B1561.accepted = true := by decide +kernel
theorem checked1561 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1561 (maskNeeds ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1561]
  exact B1561.sound accepted1561
#print axioms checked1561

def Tip1559_1585 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1585 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] HexagonCover.NBand.M6900_7100.SplitTree.Run0019.checked1585
def Tip1559_1561 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1561 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] checked1561
def B1580 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1580 : B1580.tree = HexagonCover.NBand.M6900_7100.SplitData.node1580 := by
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

def B1579 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1580, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1579 : B1579.tree = HexagonCover.NBand.M6900_7100.SplitData.node1579 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1580
  · rfl
  · rfl

def B1578 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1579]
theorem treeEq1578 : B1578.tree = HexagonCover.NBand.M6900_7100.SplitData.node1578 := by
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
  · exact treeEq1579

def B1584 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1584 : B1584.tree = HexagonCover.NBand.M6900_7100.SplitData.node1584 := by
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

def B1583 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1584, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1583 : B1583.tree = HexagonCover.NBand.M6900_7100.SplitData.node1583 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1584
  · rfl
  · rfl

def B1582 : Block := .branch 124 ![10384594955009694542441267557564801, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1583]
theorem treeEq1582 : B1582.tree = HexagonCover.NBand.M6900_7100.SplitData.node1582 := by
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
  · exact treeEq1583

def B1581 : Block := .branch 90 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1582, Tip1559_1585, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1581 : B1581.tree = HexagonCover.NBand.M6900_7100.SplitData.node1581 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1582
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1577 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1578, B1581, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq1577 : B1577.tree = HexagonCover.NBand.M6900_7100.SplitData.node1577 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1578
  · exact treeEq1581
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1576 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1577, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1576 : B1576.tree = HexagonCover.NBand.M6900_7100.SplitData.node1576 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1577
  · rfl
  · rfl

def B1575 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1576, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1575 : B1575.tree = HexagonCover.NBand.M6900_7100.SplitData.node1575 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1576
  · rfl

def B1574 : Block := .branch 169 ![10387129018270111715863986064851329, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309448580807785149258793024] ![B1575, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq1574 : B1574.tree = HexagonCover.NBand.M6900_7100.SplitData.node1574 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1575
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1560 : Block := .branch 108 ![10387129018270111715863986064851329, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), Tip1559_1561, (.leaf 5 (Common.fact 322).pointIds 322), B1574]
theorem treeEq1560 : B1560.tree = HexagonCover.NBand.M6900_7100.SplitData.node1560 := by
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
  · exact treeEq1574

def B1609 : Block := .branch 164 ![93536104789220322060903422481853605844458452025729, 1538, 6148, 24584, 98320, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq1609 : B1609.tree = HexagonCover.NBand.M6900_7100.SplitData.node1609 := by
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

def B1608 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 98320, 2865645758011185073687339798035314453518876704, 21778071485792739815242086773067913625664] ![B1609, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1608 : B1608.tree = HexagonCover.NBand.M6900_7100.SplitData.node1608 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1609
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1607 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1608, (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq1607 : B1607.tree = HexagonCover.NBand.M6900_7100.SplitData.node1607 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1608
  · rfl

def B1606 : Block := .branch 166 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218545936056990610539804986644627520] ![B1607, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1606 : B1606.tree = HexagonCover.NBand.M6900_7100.SplitData.node1606 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1607
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1605 : Block := .branch 151 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1606, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1605 : B1605.tree = HexagonCover.NBand.M6900_7100.SplitData.node1605 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1606
  · rfl

def B1604 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1605, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq1604 : B1604.tree = HexagonCover.NBand.M6900_7100.SplitData.node1604 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1605
  · rfl
  · rfl

def B1559 : Block := .branch 101 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B1560, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B1604]
theorem treeEq1559 : B1559.tree = HexagonCover.NBand.M6900_7100.SplitData.node1559 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1560
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1604

theorem accepted1559 : B1559.accepted = true := by decide +kernel
theorem checked1559 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1559 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1559]
  exact B1559.sound accepted1559
#print axioms checked1559

def Tip1557_1559 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1559 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] checked1559
def B1617 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq1617 : B1617.tree = HexagonCover.NBand.M6900_7100.SplitData.node1617 := by
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

def B1616 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1617, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq1616 : B1616.tree = HexagonCover.NBand.M6900_7100.SplitData.node1616 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1617
  · rfl
  · rfl

def B1615 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1616]
theorem treeEq1615 : B1615.tree = HexagonCover.NBand.M6900_7100.SplitData.node1615 := by
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
  · exact treeEq1616

def B1614 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438614785627970074507214912] ![B1615, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1614 : B1614.tree = HexagonCover.NBand.M6900_7100.SplitData.node1614 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1615
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1613 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1614, (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq1613 : B1613.tree = HexagonCover.NBand.M6900_7100.SplitData.node1613 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1614
  · rfl

def B1612 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374760173723692130687778880] ![B1613, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1612 : B1612.tree = HexagonCover.NBand.M6900_7100.SplitData.node1612 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1613
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1611 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1612, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1611 : B1611.tree = HexagonCover.NBand.M6900_7100.SplitData.node1611 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1612
  · rfl

def B1610 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1611, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq1610 : B1610.tree = HexagonCover.NBand.M6900_7100.SplitData.node1610 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1611
  · rfl
  · rfl

def B1558 : Block := .branch 89 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip1557_1559, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B1610]
theorem treeEq1558 : B1558.tree = HexagonCover.NBand.M6900_7100.SplitData.node1558 := by
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
  · exact treeEq1610

def B1625 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq1625 : B1625.tree = HexagonCover.NBand.M6900_7100.SplitData.node1625 := by
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

def B1624 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1625, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq1624 : B1624.tree = HexagonCover.NBand.M6900_7100.SplitData.node1624 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1625
  · rfl
  · rfl

def B1623 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1624]
theorem treeEq1623 : B1623.tree = HexagonCover.NBand.M6900_7100.SplitData.node1623 := by
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
  · exact treeEq1624

def B1622 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257515986038083306341688410176] ![B1623, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1622 : B1622.tree = HexagonCover.NBand.M6900_7100.SplitData.node1622 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1623
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1621 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1622, (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1621 : B1621.tree = HexagonCover.NBand.M6900_7100.SplitData.node1621 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1622
  · rfl

def B1620 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833161406536338260419412032] ![B1621, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1620 : B1620.tree = HexagonCover.NBand.M6900_7100.SplitData.node1620 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1621
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1619 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1620, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1619 : B1619.tree = HexagonCover.NBand.M6900_7100.SplitData.node1619 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1620
  · rfl

def B1618 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1619, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq1618 : B1618.tree = HexagonCover.NBand.M6900_7100.SplitData.node1618 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1619
  · rfl
  · rfl

def B1557 : Block := .branch 86 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B1558, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B1618]
theorem treeEq1557 : B1557.tree = HexagonCover.NBand.M6900_7100.SplitData.node1557 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1558
  · rfl
  · rfl
  · exact treeEq1618

theorem accepted1557 : B1557.accepted = true := by decide +kernel
theorem checked1557 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1557 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1557]
  exact B1557.sound accepted1557
#print axioms checked1557

def Tip1505_1515 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1515 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] HexagonCover.NBand.M6900_7100.SplitTree.Run0019.checked1515
def B1514 : Block := .branch 142 ![385, 1538, 6148, 24584, 5847433797016317632695797616834581573760113016848, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq1514 : B1514.tree = HexagonCover.NBand.M6900_7100.SplitData.node1514 := by
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

def B1513 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1514, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq1513 : B1513.tree = HexagonCover.NBand.M6900_7100.SplitData.node1513 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1514
  · rfl
  · rfl

def B1512 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 1538, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1513]
theorem treeEq1512 : B1512.tree = HexagonCover.NBand.M6900_7100.SplitData.node1512 := by
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
  · exact treeEq1513

def B1511 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 302674248820119872472578, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1512, Tip1505_1515, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq1511 : B1511.tree = HexagonCover.NBand.M6900_7100.SplitData.node1511 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1512
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1555 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1555 : B1555.tree = HexagonCover.NBand.M6900_7100.SplitData.node1555 := by
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

def B1554 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1555, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1554 : B1554.tree = HexagonCover.NBand.M6900_7100.SplitData.node1554 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1555
  · rfl
  · rfl

def B1510 : Block := .branch 78 ![748288838313422304507415652621438917738182232506753, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B1511, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1554]
theorem treeEq1510 : B1510.tree = HexagonCover.NBand.M6900_7100.SplitData.node1510 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1511
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1554

def B1509 : Block := .branch 101 ![748288838313422304504880351420982458935188826096001, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1510, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq1509 : B1509.tree = HexagonCover.NBand.M6900_7100.SplitData.node1509 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1510
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1508 : Block := .branch 169 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1509, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1508 : B1508.tree = HexagonCover.NBand.M6900_7100.SplitData.node1508 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1509
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1507 : Block := .branch 109 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1508]
theorem treeEq1507 : B1507.tree = HexagonCover.NBand.M6900_7100.SplitData.node1507 := by
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
  · exact treeEq1508

def B1506 : Block := .branch 150 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1507, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1506 : B1506.tree = HexagonCover.NBand.M6900_7100.SplitData.node1506 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1507
  · rfl
  · rfl

def B1505 : Block := .branch 125 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1506, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1505 : B1505.tree = HexagonCover.NBand.M6900_7100.SplitData.node1505 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1506
  · rfl

theorem accepted1505 : B1505.accepted = true := by decide +kernel
theorem checked1505 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1505 (maskNeeds ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1505]
  exact B1505.sound accepted1505
#print axioms checked1505

end HexagonCover.NBand.M6900_7100.SplitTree.Run0020
