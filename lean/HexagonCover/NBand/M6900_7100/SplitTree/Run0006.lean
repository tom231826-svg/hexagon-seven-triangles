import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0006
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0604 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0604 : B0604.tree = HexagonCover.NBand.M6900_7100.SplitData.node0604 := by
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

def B0603 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![B0604, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq0603 : B0603.tree = HexagonCover.NBand.M6900_7100.SplitData.node0603 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0604
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0602 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B0603, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0602 : B0602.tree = HexagonCover.NBand.M6900_7100.SplitData.node0602 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0603
  · rfl
  · rfl
  · rfl
  · rfl

def B0601 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 18889465931478580879368, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0602, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0601 : B0601.tree = HexagonCover.NBand.M6900_7100.SplitData.node0601 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0602
  · rfl
  · rfl
  · rfl
  · rfl

def B0600 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 18889465931478580879368, 5847433797016317632695797616834581573760113016848, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0601, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0600 : B0600.tree = HexagonCover.NBand.M6900_7100.SplitData.node0600 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0601
  · rfl
  · rfl
  · rfl

def B0599 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 719).pointIds 719), B0600, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq0599 : B0599.tree = HexagonCover.NBand.M6900_7100.SplitData.node0599 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0600
  · rfl
  · rfl

def B0598 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0599]
theorem treeEq0598 : B0598.tree = HexagonCover.NBand.M6900_7100.SplitData.node0598 := by
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
  · exact treeEq0599

def B0597 : Block := .branch 166 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309448580807785149258793024] ![B0598, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0597 : B0597.tree = HexagonCover.NBand.M6900_7100.SplitData.node0597 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0598
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0596 : Block := .branch 151 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0597, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0596 : B0596.tree = HexagonCover.NBand.M6900_7100.SplitData.node0596 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0597
  · rfl

def B0608 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0608 : B0608.tree = HexagonCover.NBand.M6900_7100.SplitData.node0608 := by
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

def B0607 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0608, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq0607 : B0607.tree = HexagonCover.NBand.M6900_7100.SplitData.node0607 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0608
  · rfl
  · rfl

def B0606 : Block := .branch 159 ![748288838313443577345109768609186252568290935177601, 1033089726821284447746, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0607]
theorem treeEq0606 : B0606.tree = HexagonCover.NBand.M6900_7100.SplitData.node0606 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0607

def B0610 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0610 : B0610.tree = HexagonCover.NBand.M6900_7100.SplitData.node0610 := by
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

def B0609 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0610, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq0609 : B0609.tree = HexagonCover.NBand.M6900_7100.SplitData.node0609 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0610
  · rfl
  · rfl

def B0605 : Block := .branch 124 ![748288838313422309697177209955219791655326449664385, 1033089726821284447746, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![B0606, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0609]
theorem treeEq0605 : B0605.tree = HexagonCover.NBand.M6900_7100.SplitData.node0605 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0606
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0609

def B0595 : Block := .branch 119 ![748288838313422309697177209955219791655326449664385, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0596, (.leaf 5 (Common.fact 163).pointIds 163), B0605]
theorem treeEq0595 : B0595.tree = HexagonCover.NBand.M6900_7100.SplitData.node0595 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0596
  · rfl
  · exact treeEq0605

def B0612 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq0612 : B0612.tree = HexagonCover.NBand.M6900_7100.SplitData.node0612 := by
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

def B0611 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0612, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0611 : B0611.tree = HexagonCover.NBand.M6900_7100.SplitData.node0611 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0612
  · rfl
  · rfl

def B0594 : Block := .branch 112 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0595, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0611]
theorem treeEq0594 : B0594.tree = HexagonCover.NBand.M6900_7100.SplitData.node0594 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0595
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0611

theorem accepted0594 : B0594.accepted = true := by decide +kernel
theorem checked0594 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0594 (maskNeeds ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024]) := by
  rw [← treeEq0594]
  exact B0594.sound accepted0594
#print axioms checked0594

def B0582 : Block := .branch 124 ![94266855607843238224137671710200254767807649022337, 1538, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0582 : B0582.tree = HexagonCover.NBand.M6900_7100.SplitData.node0582 := by
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

def B0581 : Block := .branch 159 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![B0582, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0581 : B0581.tree = HexagonCover.NBand.M6900_7100.SplitData.node0581 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0582
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0580 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B0581, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq0580 : B0580.tree = HexagonCover.NBand.M6900_7100.SplitData.node0580 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0581
  · rfl
  · rfl
  · rfl
  · rfl

def B0579 : Block := .branch 161 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 18889465931478580879368, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0580, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0579 : B0579.tree = HexagonCover.NBand.M6900_7100.SplitData.node0579 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0580
  · rfl
  · rfl
  · rfl
  · rfl

def B0578 : Block := .branch 137 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 18889465931478580879368, 5847433797016317632695797616834581573760113016848, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0579, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0578 : B0578.tree = HexagonCover.NBand.M6900_7100.SplitData.node0578 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0579
  · rfl
  · rfl
  · rfl

def B0577 : Block := .branch 162 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 719).pointIds 719), B0578, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0577 : B0577.tree = HexagonCover.NBand.M6900_7100.SplitData.node0577 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0578
  · rfl
  · rfl

def B0576 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 18889465931478580879368, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 482).pointIds 482), B0577]
theorem treeEq0576 : B0576.tree = HexagonCover.NBand.M6900_7100.SplitData.node0576 := by
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
  · exact treeEq0577

def B0575 : Block := .branch 150 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 18889465931478580879368, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0576, (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0575 : B0575.tree = HexagonCover.NBand.M6900_7100.SplitData.node0575 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0576
  · rfl
  · rfl

def B0574 : Block := .branch 125 ![841824943102600080887857764845035478124810551165313, 737941821641931621890, 6148, 18889465931478580879368, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0575, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0574 : B0574.tree = HexagonCover.NBand.M6900_7100.SplitData.node0574 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0575
  · rfl

def B0573 : Block := .branch 169 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![B0574, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 687).pointIds 687)]
theorem treeEq0573 : B0573.tree = HexagonCover.NBand.M6900_7100.SplitData.node0573 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0574
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0572 : Block := .branch 142 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B0573]
theorem treeEq0572 : B0572.tree = HexagonCover.NBand.M6900_7100.SplitData.node0572 := by
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
  · exact treeEq0573

def B0571 : Block := .branch 166 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755790154081001993238216768] ![B0572, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0571 : B0571.tree = HexagonCover.NBand.M6900_7100.SplitData.node0571 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0572
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0570 : Block := .branch 151 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B0571, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0570 : B0570.tree = HexagonCover.NBand.M6900_7100.SplitData.node0570 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0571
  · rfl

theorem accepted0570 : B0570.accepted = true := by decide +kernel
theorem checked0570 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0570 (maskNeeds ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0570]
  exact B0570.sound accepted0570
#print axioms checked0570

def Tip0568_0594 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0594 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] checked0594
def Tip0568_0570 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0570 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] checked0570
def B0589 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0589 : B0589.tree = HexagonCover.NBand.M6900_7100.SplitData.node0589 := by
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

def B0588 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0589, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0588 : B0588.tree = HexagonCover.NBand.M6900_7100.SplitData.node0588 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0589
  · rfl
  · rfl

def B0587 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0588]
theorem treeEq0587 : B0587.tree = HexagonCover.NBand.M6900_7100.SplitData.node0587 := by
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
  · exact treeEq0588

def B0593 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0593 : B0593.tree = HexagonCover.NBand.M6900_7100.SplitData.node0593 := by
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

def B0592 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0593, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0592 : B0592.tree = HexagonCover.NBand.M6900_7100.SplitData.node0592 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0593
  · rfl
  · rfl

def B0591 : Block := .branch 124 ![10384594955009694542441267557564801, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0592]
theorem treeEq0591 : B0591.tree = HexagonCover.NBand.M6900_7100.SplitData.node0591 := by
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
  · exact treeEq0592

def B0590 : Block := .branch 90 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0591, Tip0568_0594, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq0590 : B0590.tree = HexagonCover.NBand.M6900_7100.SplitData.node0590 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0591
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0586 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0587, B0590, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0586 : B0586.tree = HexagonCover.NBand.M6900_7100.SplitData.node0586 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0587
  · exact treeEq0590
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0585 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0586, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0585 : B0585.tree = HexagonCover.NBand.M6900_7100.SplitData.node0585 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0586
  · rfl
  · rfl

def B0584 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 11842809695321532143620, 38704515693599612171477000, 98320, 393248, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0585, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0584 : B0584.tree = HexagonCover.NBand.M6900_7100.SplitData.node0584 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0585
  · rfl

def B0583 : Block := .branch 169 ![10387129018270111715863986064851329, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309448580807785149258793024] ![B0584, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0583 : B0583.tree = HexagonCover.NBand.M6900_7100.SplitData.node0583 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0584
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0569 : Block := .branch 108 ![10387129018270111715863986064851329, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), Tip0568_0570, (.leaf 5 (Common.fact 322).pointIds 322), B0583]
theorem treeEq0569 : B0569.tree = HexagonCover.NBand.M6900_7100.SplitData.node0569 := by
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
  · exact treeEq0583

def B0618 : Block := .branch 164 ![93536104789220322060903422481853605844458452025729, 1538, 6148, 24584, 98320, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq0618 : B0618.tree = HexagonCover.NBand.M6900_7100.SplitData.node0618 := by
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

def B0617 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 98320, 2865645758011185073687339798035314453518876704, 21778071485792739815242086773067913625664] ![B0618, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0617 : B0617.tree = HexagonCover.NBand.M6900_7100.SplitData.node0617 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0618
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0616 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0617, (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0616 : B0616.tree = HexagonCover.NBand.M6900_7100.SplitData.node0616 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0617
  · rfl

def B0615 : Block := .branch 166 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218545936056990610539804986644627520] ![B0616, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0615 : B0615.tree = HexagonCover.NBand.M6900_7100.SplitData.node0615 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0616
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0614 : Block := .branch 151 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0615, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0614 : B0614.tree = HexagonCover.NBand.M6900_7100.SplitData.node0614 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0615
  · rfl

def B0613 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 98320, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0614, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq0613 : B0613.tree = HexagonCover.NBand.M6900_7100.SplitData.node0613 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0614
  · rfl
  · rfl

def B0568 : Block := .branch 101 ![10384596192949733827821542456689025, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B0569, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B0613]
theorem treeEq0568 : B0568.tree = HexagonCover.NBand.M6900_7100.SplitData.node0568 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0569
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0613

theorem accepted0568 : B0568.accepted = true := by decide +kernel
theorem checked0568 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0568 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0568]
  exact B0568.sound accepted0568
#print axioms checked0568

def Tip0566_0568 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0568 ![10384596192949733827821542456689025, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] checked0568
def B0626 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0626 : B0626.tree = HexagonCover.NBand.M6900_7100.SplitData.node0626 := by
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

def B0625 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0626, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq0625 : B0625.tree = HexagonCover.NBand.M6900_7100.SplitData.node0625 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0626
  · rfl
  · rfl

def B0624 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0625]
theorem treeEq0624 : B0624.tree = HexagonCover.NBand.M6900_7100.SplitData.node0624 := by
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
  · exact treeEq0625

def B0623 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438614785627970074507214912] ![B0624, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0623 : B0623.tree = HexagonCover.NBand.M6900_7100.SplitData.node0623 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0624
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0622 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0623, (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq0622 : B0622.tree = HexagonCover.NBand.M6900_7100.SplitData.node0622 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0623
  · rfl

def B0621 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374760173723692130687778880] ![B0622, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0621 : B0621.tree = HexagonCover.NBand.M6900_7100.SplitData.node0621 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0622
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0620 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0621, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0620 : B0620.tree = HexagonCover.NBand.M6900_7100.SplitData.node0620 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0621
  · rfl

def B0619 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0620, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq0619 : B0619.tree = HexagonCover.NBand.M6900_7100.SplitData.node0619 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0620
  · rfl
  · rfl

def B0567 : Block := .branch 89 ![10384596192949733827821542456689025, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip0566_0568, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0619]
theorem treeEq0567 : B0567.tree = HexagonCover.NBand.M6900_7100.SplitData.node0567 := by
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
  · exact treeEq0619

def B0634 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq0634 : B0634.tree = HexagonCover.NBand.M6900_7100.SplitData.node0634 := by
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

def B0633 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0634, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq0633 : B0633.tree = HexagonCover.NBand.M6900_7100.SplitData.node0633 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0634
  · rfl
  · rfl

def B0632 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0633]
theorem treeEq0632 : B0632.tree = HexagonCover.NBand.M6900_7100.SplitData.node0632 := by
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
  · exact treeEq0633

def B0631 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257515986038083306341688410176] ![B0632, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0631 : B0631.tree = HexagonCover.NBand.M6900_7100.SplitData.node0631 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0632
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0630 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0631, (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0630 : B0630.tree = HexagonCover.NBand.M6900_7100.SplitData.node0630 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0631
  · rfl

def B0629 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833161406536338260419412032] ![B0630, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0629 : B0629.tree = HexagonCover.NBand.M6900_7100.SplitData.node0629 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0630
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0628 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0629, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0628 : B0628.tree = HexagonCover.NBand.M6900_7100.SplitData.node0628 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0629
  · rfl

def B0627 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0628, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0627 : B0627.tree = HexagonCover.NBand.M6900_7100.SplitData.node0627 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0628
  · rfl
  · rfl

def B0566 : Block := .branch 86 ![10384596192949733827821542456689025, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B0567, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0627]
theorem treeEq0566 : B0566.tree = HexagonCover.NBand.M6900_7100.SplitData.node0566 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0567
  · rfl
  · rfl
  · exact treeEq0627

theorem accepted0566 : B0566.accepted = true := by decide +kernel
theorem checked0566 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0566 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0566]
  exact B0566.sound accepted0566
#print axioms checked0566

end HexagonCover.NBand.M6900_7100.SplitTree.Run0006
