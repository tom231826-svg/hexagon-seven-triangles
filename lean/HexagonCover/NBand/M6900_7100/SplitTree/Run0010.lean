import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0008
import HexagonCover.NBand.M6900_7100.SplitTree.Run0009
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0010
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0816_0842 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0842 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] HexagonCover.NBand.M6900_7100.SplitTree.Run0009.checked0842
def Tip0816_0818 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0818 ![2535301200456458802993406411137, 738806512770386757122, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0009.checked0818
def B0837 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0837 : B0837.tree = HexagonCover.NBand.M6900_7100.SplitData.node0837 := by
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

def B0836 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0837, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0836 : B0836.tree = HexagonCover.NBand.M6900_7100.SplitData.node0836 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0837
  · rfl
  · rfl

def B0835 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0836]
theorem treeEq0835 : B0835.tree = HexagonCover.NBand.M6900_7100.SplitData.node0835 := by
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
  · exact treeEq0836

def B0841 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq0841 : B0841.tree = HexagonCover.NBand.M6900_7100.SplitData.node0841 := by
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

def B0840 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0841, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0840 : B0840.tree = HexagonCover.NBand.M6900_7100.SplitData.node0840 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0841
  · rfl
  · rfl

def B0839 : Block := .branch 124 ![10384594955009694542441267557564801, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0840]
theorem treeEq0839 : B0839.tree = HexagonCover.NBand.M6900_7100.SplitData.node0839 := by
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
  · exact treeEq0840

def B0838 : Block := .branch 90 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0839, Tip0816_0842, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq0838 : B0838.tree = HexagonCover.NBand.M6900_7100.SplitData.node0838 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0839
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0834 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B0835, B0838, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0834 : B0834.tree = HexagonCover.NBand.M6900_7100.SplitData.node0834 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0835
  · exact treeEq0838
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0833 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0834, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0833 : B0833.tree = HexagonCover.NBand.M6900_7100.SplitData.node0833 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0834
  · rfl
  · rfl

def B0832 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0833, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0832 : B0832.tree = HexagonCover.NBand.M6900_7100.SplitData.node0832 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0833
  · rfl

def B0831 : Block := .branch 169 ![10387129018270111715863986064851329, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309448580807785149258793024] ![B0832, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0831 : B0831.tree = HexagonCover.NBand.M6900_7100.SplitData.node0831 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0832
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0817 : Block := .branch 108 ![10387129018270111715863986064851329, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), Tip0816_0818, (.leaf 5 (Common.fact 322).pointIds 322), B0831]
theorem treeEq0817 : B0817.tree = HexagonCover.NBand.M6900_7100.SplitData.node0817 := by
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
  · exact treeEq0831

def B0866 : Block := .branch 164 ![93536104789220322060903422481853605844458452025729, 1538, 6148, 24584, 98320, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 698).pointIds 698), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq0866 : B0866.tree = HexagonCover.NBand.M6900_7100.SplitData.node0866 := by
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

def B0865 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 98320, 2865645758011185073687339798035314453518876704, 21778071485792739815242086773067913625664] ![B0866, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0865 : B0865.tree = HexagonCover.NBand.M6900_7100.SplitData.node0865 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0866
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0864 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0865, (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0864 : B0864.tree = HexagonCover.NBand.M6900_7100.SplitData.node0864 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0865
  · rfl

def B0863 : Block := .branch 166 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 2854495385411919762116571938898990272765886496, 374144419178489218545936056990610539804986644627520] ![B0864, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0863 : B0863.tree = HexagonCover.NBand.M6900_7100.SplitData.node0863 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0864
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0862 : Block := .branch 151 ![2475880078570760549798248833, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0863, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0862 : B0862.tree = HexagonCover.NBand.M6900_7100.SplitData.node0862 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0863
  · rfl

def B0861 : Block := .branch 170 ![10384596192949733827821542456689025, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218545936056990610539804986644627520] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0862, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq0861 : B0861.tree = HexagonCover.NBand.M6900_7100.SplitData.node0861 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0862
  · rfl
  · rfl

def B0816 : Block := .branch 101 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B0817, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B0861]
theorem treeEq0816 : B0816.tree = HexagonCover.NBand.M6900_7100.SplitData.node0816 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0817
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0861

theorem accepted0816 : B0816.accepted = true := by decide +kernel
theorem checked0816 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0816 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0816]
  exact B0816.sound accepted0816
#print axioms checked0816

def Tip0814_0816 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0816 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] checked0816
def B0874 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0874 : B0874.tree = HexagonCover.NBand.M6900_7100.SplitData.node0874 := by
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

def B0873 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0874, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq0873 : B0873.tree = HexagonCover.NBand.M6900_7100.SplitData.node0873 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0874
  · rfl
  · rfl

def B0872 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0873]
theorem treeEq0872 : B0872.tree = HexagonCover.NBand.M6900_7100.SplitData.node0872 := by
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
  · exact treeEq0873

def B0871 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438614785627970074507214912] ![B0872, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0871 : B0871.tree = HexagonCover.NBand.M6900_7100.SplitData.node0871 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0872
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0870 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0871, (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq0870 : B0870.tree = HexagonCover.NBand.M6900_7100.SplitData.node0870 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0871
  · rfl

def B0869 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374760173723692130687778880] ![B0870, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0869 : B0869.tree = HexagonCover.NBand.M6900_7100.SplitData.node0869 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0870
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0868 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0869, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0868 : B0868.tree = HexagonCover.NBand.M6900_7100.SplitData.node0868 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0869
  · rfl

def B0867 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0868, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq0867 : B0867.tree = HexagonCover.NBand.M6900_7100.SplitData.node0867 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0868
  · rfl
  · rfl

def B0815 : Block := .branch 89 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip0814_0816, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0867]
theorem treeEq0815 : B0815.tree = HexagonCover.NBand.M6900_7100.SplitData.node0815 := by
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
  · exact treeEq0867

def B0882 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq0882 : B0882.tree = HexagonCover.NBand.M6900_7100.SplitData.node0882 := by
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

def B0881 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0882, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq0881 : B0881.tree = HexagonCover.NBand.M6900_7100.SplitData.node0881 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0882
  · rfl
  · rfl

def B0880 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0881]
theorem treeEq0880 : B0880.tree = HexagonCover.NBand.M6900_7100.SplitData.node0880 := by
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
  · exact treeEq0881

def B0879 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257515986038083306341688410176] ![B0880, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0879 : B0879.tree = HexagonCover.NBand.M6900_7100.SplitData.node0879 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0880
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0878 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0879, (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0878 : B0878.tree = HexagonCover.NBand.M6900_7100.SplitData.node0878 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0879
  · rfl

def B0877 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833161406536338260419412032] ![B0878, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0877 : B0877.tree = HexagonCover.NBand.M6900_7100.SplitData.node0877 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0878
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0876 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0877, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0876 : B0876.tree = HexagonCover.NBand.M6900_7100.SplitData.node0876 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0877
  · rfl

def B0875 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0876, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0875 : B0875.tree = HexagonCover.NBand.M6900_7100.SplitData.node0875 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0876
  · rfl
  · rfl

def B0814 : Block := .branch 86 ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B0815, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0875]
theorem treeEq0814 : B0814.tree = HexagonCover.NBand.M6900_7100.SplitData.node0814 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0815
  · rfl
  · rfl
  · exact treeEq0875

theorem accepted0814 : B0814.accepted = true := by decide +kernel
theorem checked0814 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0814 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0814]
  exact B0814.sound accepted0814
#print axioms checked0814

def Tip0762_0772 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0772 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] HexagonCover.NBand.M6900_7100.SplitTree.Run0009.checked0772
def B0771 : Block := .branch 142 ![385, 1538, 6148, 24584, 5847433797016317632695797616834581573760113016848, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq0771 : B0771.tree = HexagonCover.NBand.M6900_7100.SplitData.node0771 := by
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

def B0770 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B0771, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq0770 : B0770.tree = HexagonCover.NBand.M6900_7100.SplitData.node0770 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0771
  · rfl
  · rfl

def B0769 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 1538, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0770]
theorem treeEq0769 : B0769.tree = HexagonCover.NBand.M6900_7100.SplitData.node0769 := by
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
  · exact treeEq0770

def B0768 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 302674248820119872472578, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B0769, Tip0762_0772, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq0768 : B0768.tree = HexagonCover.NBand.M6900_7100.SplitData.node0768 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0769
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0812 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0812 : B0812.tree = HexagonCover.NBand.M6900_7100.SplitData.node0812 := by
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

def B0811 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0812, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0811 : B0811.tree = HexagonCover.NBand.M6900_7100.SplitData.node0811 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0812
  · rfl
  · rfl

def B0767 : Block := .branch 78 ![748288838313422304507415652621438917738182232506753, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B0768, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B0811]
theorem treeEq0767 : B0767.tree = HexagonCover.NBand.M6900_7100.SplitData.node0767 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0768
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0811

def B0766 : Block := .branch 101 ![748288838313422304504880351420982458935188826096001, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B0767, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0766 : B0766.tree = HexagonCover.NBand.M6900_7100.SplitData.node0766 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0767
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0765 : Block := .branch 169 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B0766, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0765 : B0765.tree = HexagonCover.NBand.M6900_7100.SplitData.node0765 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0766
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0764 : Block := .branch 109 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0765]
theorem treeEq0764 : B0764.tree = HexagonCover.NBand.M6900_7100.SplitData.node0764 := by
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
  · exact treeEq0765

def B0763 : Block := .branch 150 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0764, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0763 : B0763.tree = HexagonCover.NBand.M6900_7100.SplitData.node0763 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0764
  · rfl
  · rfl

def B0762 : Block := .branch 125 ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0763, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0762 : B0762.tree = HexagonCover.NBand.M6900_7100.SplitData.node0762 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0763
  · rfl

theorem accepted0762 : B0762.accepted = true := by decide +kernel
theorem checked0762 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0762 (maskNeeds ![10384593717070245552871351364092289, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0762]
  exact B0762.sound accepted0762
#print axioms checked0762

def Tip0645_0647 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0647 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0008.checked0647
def B0751 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468372414128216807114477103961150943789088, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 736).pointIds 736), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0751 : B0751.tree = HexagonCover.NBand.M6900_7100.SplitData.node0751 := by
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

def B0750 : Block := .branch 125 ![841824943102600080885322463644579019321817144754561, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468329878832351689806544182135221972762656, 385836432277136441889030311747578936769593556336704] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0751, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0750 : B0750.tree = HexagonCover.NBand.M6900_7100.SplitData.node0750 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0751
  · rfl

def B0749 : Block := .branch 169 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 233843116468329878832351689806544182135221972762656, 385836432277136441889030311747578936769593556336704] ![B0750, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0749 : B0749.tree = HexagonCover.NBand.M6900_7100.SplitData.node0749 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0750
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0748 : Block := .branch 163 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 233843116468329878832351689806544182135221972762656, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B0749]
theorem treeEq0748 : B0748.tree = HexagonCover.NBand.M6900_7100.SplitData.node0748 := by
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
  · exact treeEq0749

def B0747 : Block := .branch 165 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 187075064073740985449833775159623125506232131387424, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B0748, (.leaf 0 [] 0)]
theorem treeEq0747 : B0747.tree = HexagonCover.NBand.M6900_7100.SplitData.node0747 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0748
  · rfl

def B0746 : Block := .branch 167 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B0747, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0746 : B0746.tree = HexagonCover.NBand.M6900_7100.SplitData.node0746 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0747
  · rfl

def B0745 : Block := .branch 142 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0746, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq0745 : B0745.tree = HexagonCover.NBand.M6900_7100.SplitData.node0745 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0746
  · rfl
  · rfl

def B0744 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![B0745, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0744 : B0744.tree = HexagonCover.NBand.M6900_7100.SplitData.node0744 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0745
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0743 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0744, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0743 : B0743.tree = HexagonCover.NBand.M6900_7100.SplitData.node0743 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0744
  · rfl

def B0742 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0743, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq0742 : B0742.tree = HexagonCover.NBand.M6900_7100.SplitData.node0742 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0743
  · rfl
  · rfl

def B0646 : Block := .branch 86 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), Tip0645_0647, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0742]
theorem treeEq0646 : B0646.tree = HexagonCover.NBand.M6900_7100.SplitData.node0646 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0742

def B0759 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0759 : B0759.tree = HexagonCover.NBand.M6900_7100.SplitData.node0759 := by
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

def B0758 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080882554756898504945696832] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0759, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq0758 : B0758.tree = HexagonCover.NBand.M6900_7100.SplitData.node0758 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0759
  · rfl
  · rfl

def B0757 : Block := .branch 169 ![93536104789220322060900946601775035083908653777281, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0758]
theorem treeEq0757 : B0757.tree = HexagonCover.NBand.M6900_7100.SplitData.node0757 := by
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
  · exact treeEq0758

def B0756 : Block := .branch 125 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 374144419178489218543400756016827672179736208474176] ![B0757, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0756 : B0756.tree = HexagonCover.NBand.M6900_7100.SplitData.node0756 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0757
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0755 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0756, (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq0755 : B0755.tree = HexagonCover.NBand.M6900_7100.SplitData.node0755 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0756
  · rfl

def B0754 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B0755, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0754 : B0754.tree = HexagonCover.NBand.M6900_7100.SplitData.node0754 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0755
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0753 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0754, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0753 : B0753.tree = HexagonCover.NBand.M6900_7100.SplitData.node0753 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0754
  · rfl

def B0752 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0753, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq0752 : B0752.tree = HexagonCover.NBand.M6900_7100.SplitData.node0752 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0753
  · rfl
  · rfl

def B0645 : Block := .branch 78 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), B0646, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B0752]
theorem treeEq0645 : B0645.tree = HexagonCover.NBand.M6900_7100.SplitData.node0645 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0646
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0752

theorem accepted0645 : B0645.accepted = true := by decide +kernel
theorem checked0645 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0645 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0645]
  exact B0645.sound accepted0645
#print axioms checked0645

end HexagonCover.NBand.M6900_7100.SplitTree.Run0010
