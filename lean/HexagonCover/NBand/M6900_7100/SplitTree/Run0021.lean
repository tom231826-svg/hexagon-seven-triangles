import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0017
import HexagonCover.NBand.M6900_7100.SplitTree.Run0019
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0021
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1388_1390 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1390 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0019.checked1390
def B1494 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468372414128216807114477103961150943789088, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 736).pointIds 736), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1494 : B1494.tree = HexagonCover.NBand.M6900_7100.SplitData.node1494 := by
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

def B1493 : Block := .branch 125 ![841824943102600080885322463644579019321817144754561, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468329878832351689806544182135221972762656, 385836432277136441889030311747578936769593556336704] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1494, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1493 : B1493.tree = HexagonCover.NBand.M6900_7100.SplitData.node1493 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1494
  · rfl

def B1492 : Block := .branch 169 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 233843116468329878832351689806544182135221972762656, 385836432277136441889030311747578936769593556336704] ![B1493, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1492 : B1492.tree = HexagonCover.NBand.M6900_7100.SplitData.node1492 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1493
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1491 : Block := .branch 163 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 233843116468329878832351689806544182135221972762656, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B1492]
theorem treeEq1491 : B1491.tree = HexagonCover.NBand.M6900_7100.SplitData.node1491 := by
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
  · exact treeEq1492

def B1490 : Block := .branch 165 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 187075064073740985449833775159623125506232131387424, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B1491, (.leaf 0 [] 0)]
theorem treeEq1490 : B1490.tree = HexagonCover.NBand.M6900_7100.SplitData.node1490 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1491
  · rfl

def B1489 : Block := .branch 167 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B1490, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1489 : B1489.tree = HexagonCover.NBand.M6900_7100.SplitData.node1489 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1490
  · rfl

def B1488 : Block := .branch 142 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B1489, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq1488 : B1488.tree = HexagonCover.NBand.M6900_7100.SplitData.node1488 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1489
  · rfl
  · rfl

def B1487 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![B1488, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1487 : B1487.tree = HexagonCover.NBand.M6900_7100.SplitData.node1487 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1488
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1486 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1487, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1486 : B1486.tree = HexagonCover.NBand.M6900_7100.SplitData.node1486 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1487
  · rfl

def B1485 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1486, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq1485 : B1485.tree = HexagonCover.NBand.M6900_7100.SplitData.node1485 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1486
  · rfl
  · rfl

def B1389 : Block := .branch 86 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), Tip1388_1390, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B1485]
theorem treeEq1389 : B1389.tree = HexagonCover.NBand.M6900_7100.SplitData.node1389 := by
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
  · exact treeEq1485

def B1502 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq1502 : B1502.tree = HexagonCover.NBand.M6900_7100.SplitData.node1502 := by
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

def B1501 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080882554756898504945696832] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1502, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq1501 : B1501.tree = HexagonCover.NBand.M6900_7100.SplitData.node1501 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1502
  · rfl
  · rfl

def B1500 : Block := .branch 169 ![93536104789220322060900946601775035083908653777281, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1501]
theorem treeEq1500 : B1500.tree = HexagonCover.NBand.M6900_7100.SplitData.node1500 := by
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
  · exact treeEq1501

def B1499 : Block := .branch 125 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 374144419178489218543400756016827672179736208474176] ![B1500, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1499 : B1499.tree = HexagonCover.NBand.M6900_7100.SplitData.node1499 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1500
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1498 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1499, (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq1498 : B1498.tree = HexagonCover.NBand.M6900_7100.SplitData.node1498 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1499
  · rfl

def B1497 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B1498, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1497 : B1497.tree = HexagonCover.NBand.M6900_7100.SplitData.node1497 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1498
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1496 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1497, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1496 : B1496.tree = HexagonCover.NBand.M6900_7100.SplitData.node1496 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1497
  · rfl

def B1495 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1496, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq1495 : B1495.tree = HexagonCover.NBand.M6900_7100.SplitData.node1495 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1496
  · rfl
  · rfl

def B1388 : Block := .branch 78 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), B1389, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1495]
theorem treeEq1388 : B1388.tree = HexagonCover.NBand.M6900_7100.SplitData.node1388 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1389
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1495

theorem accepted1388 : B1388.accepted = true := by decide +kernel
theorem checked1388 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1388 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1388]
  exact B1388.sound accepted1388
#print axioms checked1388

def Tip1140_1310 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1310 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0017.checked1310
def Tip1140_1258 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1258 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0017.checked1258
def Tip1140_1141 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1141 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0017.checked1141
def B1386 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq1386 : B1386.tree = HexagonCover.NBand.M6900_7100.SplitData.node1386 := by
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
  · rfl

def B1385 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 748288838335200365603543609040239256919966175723584] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1386, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1385 : B1385.tree = HexagonCover.NBand.M6900_7100.SplitData.node1385 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1386
  · rfl
  · rfl

def B1384 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1385]
theorem treeEq1384 : B1384.tree = HexagonCover.NBand.M6900_7100.SplitData.node1384 := by
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
  · exact treeEq1385

def B1383 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438917017082873731800891456] ![B1384, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1383 : B1383.tree = HexagonCover.NBand.M6900_7100.SplitData.node1383 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1384
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1382 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1383, (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq1382 : B1382.tree = HexagonCover.NBand.M6900_7100.SplitData.node1382 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1383
  · rfl

def B1381 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756092385535905650531893312] ![B1382, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1381 : B1381.tree = HexagonCover.NBand.M6900_7100.SplitData.node1381 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1382
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1380 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1381, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1380 : B1380.tree = HexagonCover.NBand.M6900_7100.SplitData.node1380 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1381
  · rfl

def B1379 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756092385535905650531893312] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1380, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq1379 : B1379.tree = HexagonCover.NBand.M6900_7100.SplitData.node1379 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1380
  · rfl
  · rfl

def B1309 : Block := .branch 78 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 146).pointIds 146), Tip1140_1310, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1379]
theorem treeEq1309 : B1309.tree = HexagonCover.NBand.M6900_7100.SplitData.node1309 := by
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
  · exact treeEq1379

def B1257 : Block := .branch 69 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![Tip1140_1258, B1309, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq1257 : B1257.tree = HexagonCover.NBand.M6900_7100.SplitData.node1257 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1309
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1256 : Block := .branch 91 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B1257, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq1256 : B1256.tree = HexagonCover.NBand.M6900_7100.SplitData.node1256 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1257
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1140 : Block := .branch 76 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip1140_1141, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B1256]
theorem treeEq1140 : B1140.tree = HexagonCover.NBand.M6900_7100.SplitData.node1140 := by
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
  · exact treeEq1256

theorem accepted1140 : B1140.accepted = true := by decide +kernel
theorem checked1140 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1140 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1140]
  exact B1140.sound accepted1140
#print axioms checked1140

def B1673 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq1673 : B1673.tree = HexagonCover.NBand.M6900_7100.SplitData.node1673 := by
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

def B1672 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B1673, (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq1672 : B1672.tree = HexagonCover.NBand.M6900_7100.SplitData.node1672 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1673
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1671 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 578).pointIds 578), B1672, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq1671 : B1671.tree = HexagonCover.NBand.M6900_7100.SplitData.node1671 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1672
  · rfl
  · rfl
  · rfl
  · rfl

def B1670 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1671, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1670 : B1670.tree = HexagonCover.NBand.M6900_7100.SplitData.node1670 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1671
  · rfl
  · rfl
  · rfl
  · rfl

def B1669 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1670, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1669 : B1669.tree = HexagonCover.NBand.M6900_7100.SplitData.node1669 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1670
  · rfl
  · rfl
  · rfl

def B1668 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1669, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq1668 : B1668.tree = HexagonCover.NBand.M6900_7100.SplitData.node1668 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1669
  · rfl
  · rfl

def B1667 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1668]
theorem treeEq1667 : B1667.tree = HexagonCover.NBand.M6900_7100.SplitData.node1667 := by
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
  · exact treeEq1668

def B1666 : Block := .branch 166 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B1667, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1666 : B1666.tree = HexagonCover.NBand.M6900_7100.SplitData.node1666 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1667
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1665 : Block := .branch 151 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1666, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1665 : B1665.tree = HexagonCover.NBand.M6900_7100.SplitData.node1665 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1666
  · rfl

def B1677 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1677 : B1677.tree = HexagonCover.NBand.M6900_7100.SplitData.node1677 := by
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

def B1676 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1677, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1676 : B1676.tree = HexagonCover.NBand.M6900_7100.SplitData.node1676 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1677
  · rfl
  · rfl

def B1675 : Block := .branch 124 ![15576891813544522170971763886784897, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1676]
theorem treeEq1675 : B1675.tree = HexagonCover.NBand.M6900_7100.SplitData.node1675 := by
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
  · exact treeEq1676

def B1681 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq1681 : B1681.tree = HexagonCover.NBand.M6900_7100.SplitData.node1681 := by
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

def B1680 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1681, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq1680 : B1680.tree = HexagonCover.NBand.M6900_7100.SplitData.node1680 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1681
  · rfl
  · rfl

def B1679 : Block := .branch 159 ![748288838313443577345109768609776548378649640829313, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1680]
theorem treeEq1679 : B1679.tree = HexagonCover.NBand.M6900_7100.SplitData.node1679 := by
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
  · exact treeEq1680

def B1683 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1683 : B1683.tree = HexagonCover.NBand.M6900_7100.SplitData.node1683 := by
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

def B1682 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1683, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1682 : B1682.tree = HexagonCover.NBand.M6900_7100.SplitData.node1682 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1683
  · rfl
  · rfl

def B1678 : Block := .branch 124 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1679, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1682]
theorem treeEq1678 : B1678.tree = HexagonCover.NBand.M6900_7100.SplitData.node1678 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1679
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1682

def B1674 : Block := .branch 90 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1675, B1678, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1674 : B1674.tree = HexagonCover.NBand.M6900_7100.SplitData.node1674 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1675
  · exact treeEq1678
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1664 : Block := .branch 119 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1665, (.leaf 5 (Common.fact 163).pointIds 163), B1674]
theorem treeEq1664 : B1664.tree = HexagonCover.NBand.M6900_7100.SplitData.node1664 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1665
  · rfl
  · exact treeEq1674

theorem accepted1664 : B1664.accepted = true := by decide +kernel
theorem checked1664 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1664 (maskNeeds ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq1664]
  exact B1664.sound accepted1664
#print axioms checked1664

def B1700 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq1700 : B1700.tree = HexagonCover.NBand.M6900_7100.SplitData.node1700 := by
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

def B1699 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B1700, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq1699 : B1699.tree = HexagonCover.NBand.M6900_7100.SplitData.node1699 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1700
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1698 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 600).pointIds 600), B1699, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq1698 : B1698.tree = HexagonCover.NBand.M6900_7100.SplitData.node1698 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1699
  · rfl
  · rfl
  · rfl
  · rfl

def B1697 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1698, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1697 : B1697.tree = HexagonCover.NBand.M6900_7100.SplitData.node1697 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1698
  · rfl
  · rfl
  · rfl
  · rfl

def B1696 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1697, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1696 : B1696.tree = HexagonCover.NBand.M6900_7100.SplitData.node1696 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1697
  · rfl
  · rfl
  · rfl

def B1695 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1696, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq1695 : B1695.tree = HexagonCover.NBand.M6900_7100.SplitData.node1695 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1696
  · rfl
  · rfl

def B1694 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1695]
theorem treeEq1694 : B1694.tree = HexagonCover.NBand.M6900_7100.SplitData.node1694 := by
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
  · exact treeEq1695

def B1693 : Block := .branch 166 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B1694, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1693 : B1693.tree = HexagonCover.NBand.M6900_7100.SplitData.node1693 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1694
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1692 : Block := .branch 151 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1693, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1692 : B1692.tree = HexagonCover.NBand.M6900_7100.SplitData.node1692 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1693
  · rfl

def B1704 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1704 : B1704.tree = HexagonCover.NBand.M6900_7100.SplitData.node1704 := by
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

def B1703 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1704, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1703 : B1703.tree = HexagonCover.NBand.M6900_7100.SplitData.node1703 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1704
  · rfl
  · rfl

def B1702 : Block := .branch 124 ![15576891813544522170971763886784897, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1703]
theorem treeEq1702 : B1702.tree = HexagonCover.NBand.M6900_7100.SplitData.node1702 := by
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
  · exact treeEq1703

def B1708 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq1708 : B1708.tree = HexagonCover.NBand.M6900_7100.SplitData.node1708 := by
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

def B1707 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1708, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq1707 : B1707.tree = HexagonCover.NBand.M6900_7100.SplitData.node1707 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1708
  · rfl
  · rfl

def B1706 : Block := .branch 159 ![748288838313443577345109768609186252568290935177601, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1707]
theorem treeEq1706 : B1706.tree = HexagonCover.NBand.M6900_7100.SplitData.node1706 := by
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
  · exact treeEq1707

def B1710 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1710 : B1710.tree = HexagonCover.NBand.M6900_7100.SplitData.node1710 := by
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

def B1709 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1710, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1709 : B1709.tree = HexagonCover.NBand.M6900_7100.SplitData.node1709 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1710
  · rfl
  · rfl

def B1705 : Block := .branch 124 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1706, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1709]
theorem treeEq1705 : B1705.tree = HexagonCover.NBand.M6900_7100.SplitData.node1705 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1706
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1709

def B1701 : Block := .branch 90 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1702, B1705, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1701 : B1701.tree = HexagonCover.NBand.M6900_7100.SplitData.node1701 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1702
  · exact treeEq1705
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1691 : Block := .branch 119 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1692, (.leaf 5 (Common.fact 163).pointIds 163), B1701]
theorem treeEq1691 : B1691.tree = HexagonCover.NBand.M6900_7100.SplitData.node1691 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1692
  · rfl
  · exact treeEq1701

theorem accepted1691 : B1691.accepted = true := by decide +kernel
theorem checked1691 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1691 (maskNeeds ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq1691]
  exact B1691.sound accepted1691
#print axioms checked1691

end HexagonCover.NBand.M6900_7100.SplitTree.Run0021
