import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0002
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0284_0298 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0298 ![748288838313422304504882827301061029695738624344449, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] HexagonCover.NBand.M6900_7100.SplitTree.Run0002.checked0298
def B0288 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 1496577676648643927371762801742711168993110829563968] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M6900_7100.SplitData.node0288 := by
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

def B0287 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21799339131189533041237356865435905556544] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 660).pointIds 660), B0288]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M6900_7100.SplitData.node0287 := by
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
  · exact treeEq0288

def B0286 : Block := .branch 143 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), B0287, (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M6900_7100.SplitData.node0286 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0287
  · rfl
  · rfl

def B0285 : Block := .branch 124 ![748288838313422304507418129105390102495687912456577, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0286]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M6900_7100.SplitData.node0285 := by
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
  · exact treeEq0286

def B0297 : Block := .branch 124 ![94266855607843238224137671710200254767807649022337, 1538, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M6900_7100.SplitData.node0297 := by
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

def B0296 : Block := .branch 159 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![B0297, (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M6900_7100.SplitData.node0296 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0297
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0295 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), B0296, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M6900_7100.SplitData.node0295 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0296
  · rfl
  · rfl
  · rfl
  · rfl

def B0294 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 24584, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 498).pointIds 498), B0295]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M6900_7100.SplitData.node0294 := by
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
  · exact treeEq0295

def B0293 : Block := .branch 166 ![385, 906694436769665430586882, 6148, 24584, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144419178489219192437863107007534568305279369280] ![B0294, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M6900_7100.SplitData.node0293 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0294
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0292 : Block := .branch 151 ![385, 906694436769665430586882, 6148, 24584, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 662).pointIds 662), B0293, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M6900_7100.SplitData.node0292 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0293
  · rfl

def B0291 : Block := .branch 108 ![748288838313422304504882827301061029695738624344449, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B0292, (.leaf 5 (Common.fact 322).pointIds 322), Tip0284_0298]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M6900_7100.SplitData.node0291 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0292
  · rfl
  · rfl

def B0319 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 682).pointIds 682)]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M6900_7100.SplitData.node0319 := by
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

def B0318 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0319, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 681).pointIds 681)]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M6900_7100.SplitData.node0318 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0319
  · rfl
  · rfl

def B0290 : Block := .branch 89 ![748288838313422304504882827301061029695738624344449, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 104).pointIds 104), B0291, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0318]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M6900_7100.SplitData.node0290 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0291
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0318

def B0321 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M6900_7100.SplitData.node0321 := by
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

def B0320 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0321, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M6900_7100.SplitData.node0320 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl
  · rfl

def B0289 : Block := .branch 86 ![748288838313422304504882827301061029695738624344449, 907137158627434459825666, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B0290, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0320]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M6900_7100.SplitData.node0289 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0290
  · rfl
  · rfl
  · exact treeEq0320

def B0284 : Block := .branch 79 ![748288838313422304507418128501517488498732030755201, 302674248820119872472578, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B0285, B0289, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M6900_7100.SplitData.node0284 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0285
  · exact treeEq0289
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0284 : B0284.accepted = true := by decide +kernel
theorem checked0284 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0284 (maskNeeds ![748288838313422304507418128501517488498732030755201, 302674248820119872472578, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280]) := by
  rw [← treeEq0284]
  exact B0284.sound accepted0284
#print axioms checked0284

def B0349 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M6900_7100.SplitData.node0349 := by
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

def B0348 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0349, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M6900_7100.SplitData.node0348 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0349
  · rfl
  · rfl

def B0347 : Block := .branch 124 ![10384597430889773113201817355813249, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0348]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M6900_7100.SplitData.node0347 := by
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
  · exact treeEq0348

def B0357 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0357 : B0357.tree = HexagonCover.NBand.M6900_7100.SplitData.node0357 := by
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

def B0356 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![B0357, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq0356 : B0356.tree = HexagonCover.NBand.M6900_7100.SplitData.node0356 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0357
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0355 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B0356, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0355 : B0355.tree = HexagonCover.NBand.M6900_7100.SplitData.node0355 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0356
  · rfl
  · rfl
  · rfl
  · rfl

def B0354 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0355]
theorem treeEq0354 : B0354.tree = HexagonCover.NBand.M6900_7100.SplitData.node0354 := by
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
  · exact treeEq0355

def B0353 : Block := .branch 166 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 24584, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309448580807785149258793024] ![B0354, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0353 : B0353.tree = HexagonCover.NBand.M6900_7100.SplitData.node0353 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0354
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0352 : Block := .branch 151 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0353, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0352 : B0352.tree = HexagonCover.NBand.M6900_7100.SplitData.node0352 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0353
  · rfl

def B0361 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0361 : B0361.tree = HexagonCover.NBand.M6900_7100.SplitData.node0361 := by
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

def B0360 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0361, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq0360 : B0360.tree = HexagonCover.NBand.M6900_7100.SplitData.node0360 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0361
  · rfl
  · rfl

def B0359 : Block := .branch 159 ![748288838313443577345112244489264823328840733426049, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0360]
theorem treeEq0359 : B0359.tree = HexagonCover.NBand.M6900_7100.SplitData.node0359 := by
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
  · exact treeEq0360

def B0363 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0363 : B0363.tree = HexagonCover.NBand.M6900_7100.SplitData.node0363 := by
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

def B0362 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0363, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq0362 : B0362.tree = HexagonCover.NBand.M6900_7100.SplitData.node0362 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0363
  · rfl
  · rfl

def B0358 : Block := .branch 124 ![748288838313422309697179685835298362415876247912833, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![B0359, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0362]
theorem treeEq0358 : B0358.tree = HexagonCover.NBand.M6900_7100.SplitData.node0358 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0359
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0362

def B0351 : Block := .branch 119 ![748288838313422309697179685835298362415876247912833, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0352, (.leaf 5 (Common.fact 163).pointIds 163), B0358]
theorem treeEq0351 : B0351.tree = HexagonCover.NBand.M6900_7100.SplitData.node0351 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0352
  · rfl
  · exact treeEq0358

def B0365 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq0365 : B0365.tree = HexagonCover.NBand.M6900_7100.SplitData.node0365 := by
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

def B0364 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0365, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0364 : B0364.tree = HexagonCover.NBand.M6900_7100.SplitData.node0364 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0365
  · rfl
  · rfl

def B0350 : Block := .branch 112 ![748288838313422304504882827300470733885379918692737, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0351, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0364]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M6900_7100.SplitData.node0350 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0351
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0364

def B0346 : Block := .branch 90 ![748288838313422304504882827300470733885379918692737, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0347, B0350, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M6900_7100.SplitData.node0346 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0347
  · exact treeEq0350
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0346 : B0346.accepted = true := by decide +kernel
theorem checked0346 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0346 (maskNeeds ![748288838313422304504882827300470733885379918692737, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024]) := by
  rw [← treeEq0346]
  exact B0346.sound accepted0346
#print axioms checked0346

def Tip0328_0346 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0346 ![748288838313422304504882827300470733885379918692737, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] checked0346
def B0338 : Block := .branch 124 ![94266855607843238224137671710200254767807649022337, 1538, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M6900_7100.SplitData.node0338 := by
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

def B0337 : Block := .branch 159 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![B0338, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M6900_7100.SplitData.node0337 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0338
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0336 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 98320, 393248, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B0337, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M6900_7100.SplitData.node0336 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0337
  · rfl
  · rfl
  · rfl
  · rfl

def B0335 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 5596964371115912759771200464114561796538432] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 482).pointIds 482), B0336]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M6900_7100.SplitData.node0335 := by
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
  · exact treeEq0336

def B0334 : Block := .branch 150 ![93536104789177786765035829293842113257979682750849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0335, (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M6900_7100.SplitData.node0334 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · rfl
  · rfl

def B0333 : Block := .branch 125 ![841824943102600080887857764845035478124810551165313, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0334, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M6900_7100.SplitData.node0333 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0334
  · rfl

def B0332 : Block := .branch 169 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 5596964371115913223998715196132164883710016] ![B0333, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 687).pointIds 687)]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M6900_7100.SplitData.node0332 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0333
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0331 : Block := .branch 142 ![93536104789177786767571130494298572060973089161601, 738806512770386757122, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B0332]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M6900_7100.SplitData.node0331 := by
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
  · exact treeEq0332

def B0330 : Block := .branch 166 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755790154081001993238216768] ![B0331, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M6900_7100.SplitData.node0330 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0331
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0329 : Block := .branch 151 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B0330, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M6900_7100.SplitData.node0329 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330
  · rfl

def B0345 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M6900_7100.SplitData.node0345 := by
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

def B0344 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0345, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M6900_7100.SplitData.node0344 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345
  · rfl
  · rfl

def B0343 : Block := .branch 124 ![748288838313422304507418129105390102495687912456577, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0344]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M6900_7100.SplitData.node0343 := by
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
  · exact treeEq0344

def B0342 : Block := .branch 79 ![748288838313422304507418128500927192688373325103489, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0343, Tip0328_0346, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M6900_7100.SplitData.node0342 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0343
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0341 : Block := .branch 150 ![748288838313422304507418128500927192688373325103489, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0342, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M6900_7100.SplitData.node0341 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0342
  · rfl
  · rfl

def B0340 : Block := .branch 125 ![748288838313422304507418128500927192688373325103489, 1033089726821284447746, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0341, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M6900_7100.SplitData.node0340 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0341
  · rfl

def B0339 : Block := .branch 169 ![10387131494150190286624535863099777, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309448580807785149258793024] ![B0340, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M6900_7100.SplitData.node0339 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0340
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0328 : Block := .branch 108 ![10387131494150190286624535863099777, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B0329, (.leaf 5 (Common.fact 322).pointIds 322), B0339]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M6900_7100.SplitData.node0328 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0329
  · rfl
  · exact treeEq0339

theorem accepted0328 : B0328.accepted = true := by decide +kernel
theorem checked0328 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0328 (maskNeeds ![10387131494150190286624535863099777, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0328]
  exact B0328.sound accepted0328
#print axioms checked0328

def Tip0326_0328 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0328 ![10387131494150190286624535863099777, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] checked0328
def B0371 : Block := .branch 164 ![93536104789220322060903422481853605844458452025729, 1538, 6148, 24584, 98320, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M6900_7100.SplitData.node0371 := by
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

def B0370 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 98320, 2865645758011185073687339798035314453518876704, 21778071485792739815242086773067913625664] ![B0371, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M6900_7100.SplitData.node0370 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0371
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0369 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0370, (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M6900_7100.SplitData.node0369 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0370
  · rfl

def B0368 : Block := .branch 166 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218545936056990610539804986644627520] ![B0369, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M6900_7100.SplitData.node0368 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0369
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0367 : Block := .branch 151 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0368, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M6900_7100.SplitData.node0367 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0368
  · rfl

def B0366 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 21287542661060822571012, 38685626227668133590622216, 98320, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0367, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq0366 : B0366.tree = HexagonCover.NBand.M6900_7100.SplitData.node0366 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0367
  · rfl
  · rfl

def B0327 : Block := .branch 101 ![10384596192949733827821542456689025, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip0326_0328, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B0366]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M6900_7100.SplitData.node0327 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0366

def B0379 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M6900_7100.SplitData.node0379 := by
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

def B0378 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0379, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M6900_7100.SplitData.node0378 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0379
  · rfl
  · rfl

def B0377 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0378]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M6900_7100.SplitData.node0377 := by
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
  · exact treeEq0378

def B0376 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438614785627970074507214912] ![B0377, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M6900_7100.SplitData.node0376 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0377
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0375 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0376, (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M6900_7100.SplitData.node0375 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0376
  · rfl

def B0374 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374760173723692130687778880] ![B0375, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M6900_7100.SplitData.node0374 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0375
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0373 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0374, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M6900_7100.SplitData.node0373 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0374
  · rfl

def B0372 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0373, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M6900_7100.SplitData.node0372 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0373
  · rfl
  · rfl

def B0326 : Block := .branch 89 ![10384596192949733827821542456689025, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 104).pointIds 104), B0327, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0372]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M6900_7100.SplitData.node0326 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0327
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0372

theorem accepted0326 : B0326.accepted = true := by decide +kernel
theorem checked0326 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0326 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0326]
  exact B0326.sound accepted0326
#print axioms checked0326

end HexagonCover.NBand.M6900_7100.SplitTree.Run0003
