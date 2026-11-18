import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0003
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0324_0326 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0326 ![10384596192949733827821542456689025, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0003.checked0326
def B0387 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M6900_7100.SplitData.node0387 := by
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

def B0386 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0387, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M6900_7100.SplitData.node0386 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0387
  · rfl
  · rfl

def B0385 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0386]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M6900_7100.SplitData.node0385 := by
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
  · exact treeEq0386

def B0384 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257515986038083306341688410176] ![B0385, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M6900_7100.SplitData.node0384 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0385
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0383 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0384, (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M6900_7100.SplitData.node0383 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0384
  · rfl

def B0382 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833161406536338260419412032] ![B0383, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M6900_7100.SplitData.node0382 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0383
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0381 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0382, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M6900_7100.SplitData.node0381 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0382
  · rfl

def B0380 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0381, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M6900_7100.SplitData.node0380 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0381
  · rfl
  · rfl

def B0325 : Block := .branch 86 ![10384596192949733827821542456689025, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), Tip0324_0326, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B0380]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M6900_7100.SplitData.node0325 := by
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
  · exact treeEq0380

def B0395 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2658455991569831745807614120560787472, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M6900_7100.SplitData.node0395 := by
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

def B0394 : Block := .branch 121 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 711).pointIds 711), (.leaf 1 (Common.fact 712).pointIds 712), (.leaf 2 (Common.fact 713).pointIds 713), (.leaf 3 (Common.fact 714).pointIds 714), B0395, (.leaf 5 (Common.fact 715).pointIds 715), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M6900_7100.SplitData.node0394 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0395
  · rfl
  · rfl

def B0393 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B0394]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M6900_7100.SplitData.node0393 := by
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
  · exact treeEq0394

def B0392 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438917017082873731800891456] ![B0393, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M6900_7100.SplitData.node0392 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0393
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0391 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B0392, (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M6900_7100.SplitData.node0391 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0392
  · rfl

def B0390 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756092385535905650531893312] ![B0391, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M6900_7100.SplitData.node0390 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0391
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0389 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0390, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M6900_7100.SplitData.node0389 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0390
  · rfl

def B0388 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), B0389, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M6900_7100.SplitData.node0388 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0389
  · rfl
  · rfl

def B0324 : Block := .branch 78 ![10384596192949733827821542456689025, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 146).pointIds 146), B0325, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B0388]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M6900_7100.SplitData.node0324 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0325
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0388

theorem accepted0324 : B0324.accepted = true := by decide +kernel
theorem checked0324 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0324 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq0324]
  exact B0324.sound accepted0324
#print axioms checked0324

def B0434 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0434 : B0434.tree = HexagonCover.NBand.M6900_7100.SplitData.node0434 := by
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

def B0433 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B0434, (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0433 : B0433.tree = HexagonCover.NBand.M6900_7100.SplitData.node0433 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0434
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0432 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 578).pointIds 578), B0433, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0432 : B0432.tree = HexagonCover.NBand.M6900_7100.SplitData.node0432 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0433
  · rfl
  · rfl
  · rfl
  · rfl

def B0431 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 18889465931478580879368, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0432, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0431 : B0431.tree = HexagonCover.NBand.M6900_7100.SplitData.node0431 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0432
  · rfl
  · rfl
  · rfl
  · rfl

def B0430 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 18889465931478580879368, 5847433797016317632695797616834581573760113016848, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0431, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0430 : B0430.tree = HexagonCover.NBand.M6900_7100.SplitData.node0430 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0431
  · rfl
  · rfl
  · rfl

def B0429 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 719).pointIds 719), B0430, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq0429 : B0429.tree = HexagonCover.NBand.M6900_7100.SplitData.node0429 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0430
  · rfl
  · rfl

def B0428 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0429]
theorem treeEq0428 : B0428.tree = HexagonCover.NBand.M6900_7100.SplitData.node0428 := by
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
  · exact treeEq0429

def B0427 : Block := .branch 166 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B0428, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0427 : B0427.tree = HexagonCover.NBand.M6900_7100.SplitData.node0427 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0428
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0426 : Block := .branch 151 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0427, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0426 : B0426.tree = HexagonCover.NBand.M6900_7100.SplitData.node0426 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0427
  · rfl

def B0438 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0438 : B0438.tree = HexagonCover.NBand.M6900_7100.SplitData.node0438 := by
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

def B0437 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0438, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0437 : B0437.tree = HexagonCover.NBand.M6900_7100.SplitData.node0437 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0438
  · rfl
  · rfl

def B0436 : Block := .branch 124 ![15576891813544522170971763886784897, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0437]
theorem treeEq0436 : B0436.tree = HexagonCover.NBand.M6900_7100.SplitData.node0436 := by
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
  · exact treeEq0437

def B0442 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0442 : B0442.tree = HexagonCover.NBand.M6900_7100.SplitData.node0442 := by
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

def B0441 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0442, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq0441 : B0441.tree = HexagonCover.NBand.M6900_7100.SplitData.node0441 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0442
  · rfl
  · rfl

def B0440 : Block := .branch 159 ![748288838313443577345109768609776548378649640829313, 619574925346413914615711234, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0441]
theorem treeEq0440 : B0440.tree = HexagonCover.NBand.M6900_7100.SplitData.node0440 := by
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
  · exact treeEq0441

def B0444 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0444 : B0444.tree = HexagonCover.NBand.M6900_7100.SplitData.node0444 := by
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

def B0443 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0444, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0443 : B0443.tree = HexagonCover.NBand.M6900_7100.SplitData.node0443 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0444
  · rfl
  · rfl

def B0439 : Block := .branch 124 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0440, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0443]
theorem treeEq0439 : B0439.tree = HexagonCover.NBand.M6900_7100.SplitData.node0439 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0440
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0443

def B0435 : Block := .branch 90 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0436, B0439, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0435 : B0435.tree = HexagonCover.NBand.M6900_7100.SplitData.node0435 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0436
  · exact treeEq0439
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0425 : Block := .branch 119 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0426, (.leaf 5 (Common.fact 163).pointIds 163), B0435]
theorem treeEq0425 : B0425.tree = HexagonCover.NBand.M6900_7100.SplitData.node0425 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0426
  · rfl
  · exact treeEq0435

theorem accepted0425 : B0425.accepted = true := by decide +kernel
theorem checked0425 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0425 (maskNeeds ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0425]
  exact B0425.sound accepted0425
#print axioms checked0425

def B0461 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0461 : B0461.tree = HexagonCover.NBand.M6900_7100.SplitData.node0461 := by
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

def B0460 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B0461, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0460 : B0460.tree = HexagonCover.NBand.M6900_7100.SplitData.node0460 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0461
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0459 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 600).pointIds 600), B0460, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0459 : B0459.tree = HexagonCover.NBand.M6900_7100.SplitData.node0459 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0460
  · rfl
  · rfl
  · rfl
  · rfl

def B0458 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 18889465931478580879368, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0459, (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0458 : B0458.tree = HexagonCover.NBand.M6900_7100.SplitData.node0458 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0459
  · rfl
  · rfl
  · rfl
  · rfl

def B0457 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 18889465931478580879368, 5847433797016317632695797616834581573760113016848, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0458, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0457 : B0457.tree = HexagonCover.NBand.M6900_7100.SplitData.node0457 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0458
  · rfl
  · rfl
  · rfl

def B0456 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 719).pointIds 719), B0457, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq0456 : B0456.tree = HexagonCover.NBand.M6900_7100.SplitData.node0456 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0457
  · rfl
  · rfl

def B0455 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0456]
theorem treeEq0455 : B0455.tree = HexagonCover.NBand.M6900_7100.SplitData.node0455 := by
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
  · exact treeEq0456

def B0454 : Block := .branch 166 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B0455, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0454 : B0454.tree = HexagonCover.NBand.M6900_7100.SplitData.node0454 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0455
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0453 : Block := .branch 151 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 18889465931478580879368, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0454, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0453 : B0453.tree = HexagonCover.NBand.M6900_7100.SplitData.node0453 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0454
  · rfl

def B0465 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0465 : B0465.tree = HexagonCover.NBand.M6900_7100.SplitData.node0465 := by
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

def B0464 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0465, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0464 : B0464.tree = HexagonCover.NBand.M6900_7100.SplitData.node0464 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0465
  · rfl
  · rfl

def B0463 : Block := .branch 124 ![15576891813544522170971763886784897, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0464]
theorem treeEq0463 : B0463.tree = HexagonCover.NBand.M6900_7100.SplitData.node0463 := by
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
  · exact treeEq0464

def B0469 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0469 : B0469.tree = HexagonCover.NBand.M6900_7100.SplitData.node0469 := by
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

def B0468 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0469, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq0468 : B0468.tree = HexagonCover.NBand.M6900_7100.SplitData.node0468 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0469
  · rfl
  · rfl

def B0467 : Block := .branch 159 ![748288838313443577345109768609186252568290935177601, 618971052732416958734009858, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0468]
theorem treeEq0467 : B0467.tree = HexagonCover.NBand.M6900_7100.SplitData.node0467 := by
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
  · exact treeEq0468

def B0471 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0471 : B0471.tree = HexagonCover.NBand.M6900_7100.SplitData.node0471 := by
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

def B0470 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0471, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0470 : B0470.tree = HexagonCover.NBand.M6900_7100.SplitData.node0470 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0471
  · rfl
  · rfl

def B0466 : Block := .branch 124 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0467, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0470]
theorem treeEq0466 : B0466.tree = HexagonCover.NBand.M6900_7100.SplitData.node0466 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0467
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0470

def B0462 : Block := .branch 90 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0463, B0466, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0462 : B0462.tree = HexagonCover.NBand.M6900_7100.SplitData.node0462 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0463
  · exact treeEq0466
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0452 : Block := .branch 119 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0453, (.leaf 5 (Common.fact 163).pointIds 163), B0462]
theorem treeEq0452 : B0452.tree = HexagonCover.NBand.M6900_7100.SplitData.node0452 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0453
  · rfl
  · exact treeEq0462

theorem accepted0452 : B0452.accepted = true := by decide +kernel
theorem checked0452 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0452 (maskNeeds ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0452]
  exact B0452.sound accepted0452
#print axioms checked0452

def Tip0416_0425 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0425 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] checked0425
def Tip0416_0452 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0452 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] checked0452
def B0423 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0423 : B0423.tree = HexagonCover.NBand.M6900_7100.SplitData.node0423 := by
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

def B0422 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0423, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq0422 : B0422.tree = HexagonCover.NBand.M6900_7100.SplitData.node0422 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0423
  · rfl
  · rfl

def B0421 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0422]
theorem treeEq0421 : B0421.tree = HexagonCover.NBand.M6900_7100.SplitData.node0421 := by
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
  · exact treeEq0422

def B0446 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0446 : B0446.tree = HexagonCover.NBand.M6900_7100.SplitData.node0446 := by
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

def B0445 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0446, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0445 : B0445.tree = HexagonCover.NBand.M6900_7100.SplitData.node0445 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0446
  · rfl
  · rfl

def B0424 : Block := .branch 112 ![748288838313422304504880351420982458935188826096001, 619574925346413914615711234, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![Tip0416_0425, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0445]
theorem treeEq0424 : B0424.tree = HexagonCover.NBand.M6900_7100.SplitData.node0424 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0445

def B0420 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 618970462436606600028358146, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0421, B0424, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0420 : B0420.tree = HexagonCover.NBand.M6900_7100.SplitData.node0420 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0421
  · exact treeEq0424
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0450 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0450 : B0450.tree = HexagonCover.NBand.M6900_7100.SplitData.node0450 := by
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

def B0449 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0450, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq0449 : B0449.tree = HexagonCover.NBand.M6900_7100.SplitData.node0449 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0450
  · rfl
  · rfl

def B0448 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0449]
theorem treeEq0448 : B0448.tree = HexagonCover.NBand.M6900_7100.SplitData.node0448 := by
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
  · exact treeEq0449

def B0473 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0473 : B0473.tree = HexagonCover.NBand.M6900_7100.SplitData.node0473 := by
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

def B0472 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 11842809695321532143620, 18889465931478580879368, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 725).pointIds 725), (.leaf 3 (Common.fact 726).pointIds 726), B0473, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0472 : B0472.tree = HexagonCover.NBand.M6900_7100.SplitData.node0472 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0473
  · rfl
  · rfl

def B0451 : Block := .branch 112 ![748288838313422304504880351420392163124830120444289, 618971052732416958734009858, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![Tip0416_0452, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0472]
theorem treeEq0451 : B0451.tree = HexagonCover.NBand.M6900_7100.SplitData.node0451 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0472

def B0447 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 618971052732416958734009858, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0448, B0451, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0447 : B0447.tree = HexagonCover.NBand.M6900_7100.SplitData.node0447 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0448
  · exact treeEq0451
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0419 : Block := .branch 69 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 11842809695321532143620, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0420, B0447, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0419 : B0419.tree = HexagonCover.NBand.M6900_7100.SplitData.node0419 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0420
  · exact treeEq0447
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0418 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 11842809695321532143620, 38704515693599612171477000, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0419, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0418 : B0418.tree = HexagonCover.NBand.M6900_7100.SplitData.node0418 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0419
  · rfl
  · rfl

def B0417 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 11842809695321532143620, 38704515693599612171477000, 98320, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0418, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0417 : B0417.tree = HexagonCover.NBand.M6900_7100.SplitData.node0417 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0418
  · rfl

def B0416 : Block := .branch 169 ![10387129018270111715863986064851329, 618970463301297728483493378, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B0417, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq0416 : B0416.tree = HexagonCover.NBand.M6900_7100.SplitData.node0416 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0417
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0416 : B0416.accepted = true := by decide +kernel
theorem checked0416 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0416 (maskNeeds ![10387129018270111715863986064851329, 618970463301297728483493378, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0416]
  exact B0416.sound accepted0416
#print axioms checked0416

end HexagonCover.NBand.M6900_7100.SplitTree.Run0004
