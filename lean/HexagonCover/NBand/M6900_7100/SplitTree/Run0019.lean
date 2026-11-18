import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0018
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0019
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1390_1392 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1392 ![10384593717069655257060992658440577, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0018.checked1392
def B1474 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq1474 : B1474.tree = HexagonCover.NBand.M6900_7100.SplitData.node1474 := by
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

def B1473 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1474, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq1473 : B1473.tree = HexagonCover.NBand.M6900_7100.SplitData.node1473 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1474
  · rfl
  · rfl

def B1472 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218543403231594674788036628713046080] ![B1473, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1472 : B1472.tree = HexagonCover.NBand.M6900_7100.SplitData.node1472 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1473
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1471 : Block := .branch 151 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1472, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1471 : B1471.tree = HexagonCover.NBand.M6900_7100.SplitData.node1471 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1472
  · rfl

def B1470 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1471, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1470 : B1470.tree = HexagonCover.NBand.M6900_7100.SplitData.node1470 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1471
  · rfl
  · rfl

def B1391 : Block := .branch 91 ![10384593717069655257060992658440577, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip1390_1392, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B1470]
theorem treeEq1391 : B1391.tree = HexagonCover.NBand.M6900_7100.SplitData.node1391 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1470

def B1484 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468372414128216807114477103961150943789088, 385836432277136441889030543861336302778395099922496] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 736).pointIds 736), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq1484 : B1484.tree = HexagonCover.NBand.M6900_7100.SplitData.node1484 := by
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

def B1483 : Block := .branch 125 ![841824943102600080885322463644579019321817144754561, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1484, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1483 : B1483.tree = HexagonCover.NBand.M6900_7100.SplitData.node1483 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1484
  · rfl

def B1482 : Block := .branch 169 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![B1483, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq1482 : B1482.tree = HexagonCover.NBand.M6900_7100.SplitData.node1482 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1483
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1481 : Block := .branch 163 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 233843116468329878832351689806544182135221972762656, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B1482]
theorem treeEq1481 : B1481.tree = HexagonCover.NBand.M6900_7100.SplitData.node1481 := by
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
  · exact treeEq1482

def B1480 : Block := .branch 165 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 187075064073740985449833775159623125506232131387424, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B1481, (.leaf 0 [] 0)]
theorem treeEq1480 : B1480.tree = HexagonCover.NBand.M6900_7100.SplitData.node1480 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1481
  · rfl

def B1479 : Block := .branch 167 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B1480, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1479 : B1479.tree = HexagonCover.NBand.M6900_7100.SplitData.node1479 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1480
  · rfl

def B1478 : Block := .branch 142 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B1479, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq1478 : B1478.tree = HexagonCover.NBand.M6900_7100.SplitData.node1478 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1479
  · rfl
  · rfl

def B1477 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![B1478, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1477 : B1477.tree = HexagonCover.NBand.M6900_7100.SplitData.node1477 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1478
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1476 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1477, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1476 : B1476.tree = HexagonCover.NBand.M6900_7100.SplitData.node1476 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1477
  · rfl

def B1475 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1476, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq1475 : B1475.tree = HexagonCover.NBand.M6900_7100.SplitData.node1475 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1476
  · rfl
  · rfl

def B1390 : Block := .branch 89 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), B1391, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B1475]
theorem treeEq1390 : B1390.tree = HexagonCover.NBand.M6900_7100.SplitData.node1390 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1391
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1475

theorem accepted1390 : B1390.accepted = true := by decide +kernel
theorem checked1390 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1390 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1390]
  exact B1390.sound accepted1390
#print axioms checked1390

def B1541 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1541 : B1541.tree = HexagonCover.NBand.M6900_7100.SplitData.node1541 := by
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

def B1540 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![B1541, (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1540 : B1540.tree = HexagonCover.NBand.M6900_7100.SplitData.node1540 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1541
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1539 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), B1540, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1539 : B1539.tree = HexagonCover.NBand.M6900_7100.SplitData.node1539 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1540
  · rfl
  · rfl
  · rfl
  · rfl

def B1538 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38690348594151003235835912, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1539, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1538 : B1538.tree = HexagonCover.NBand.M6900_7100.SplitData.node1538 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1539
  · rfl
  · rfl
  · rfl
  · rfl

def B1537 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1538, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1537 : B1537.tree = HexagonCover.NBand.M6900_7100.SplitData.node1537 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1538
  · rfl
  · rfl
  · rfl

def B1536 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1537, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1536 : B1536.tree = HexagonCover.NBand.M6900_7100.SplitData.node1536 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1537
  · rfl
  · rfl

def B1535 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1536]
theorem treeEq1535 : B1535.tree = HexagonCover.NBand.M6900_7100.SplitData.node1535 := by
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
  · exact treeEq1536

def B1534 : Block := .branch 166 ![5192296858534827628530496329220481, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309448580807785149258793024] ![B1535, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1534 : B1534.tree = HexagonCover.NBand.M6900_7100.SplitData.node1534 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1535
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1533 : Block := .branch 151 ![5192296858534827628530496329220481, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1534, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1533 : B1533.tree = HexagonCover.NBand.M6900_7100.SplitData.node1533 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1534
  · rfl

def B1545 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1545 : B1545.tree = HexagonCover.NBand.M6900_7100.SplitData.node1545 := by
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

def B1544 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1545, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1544 : B1544.tree = HexagonCover.NBand.M6900_7100.SplitData.node1544 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1545
  · rfl
  · rfl

def B1543 : Block := .branch 159 ![748288838313443577345109768609776548378649640829313, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1544]
theorem treeEq1543 : B1543.tree = HexagonCover.NBand.M6900_7100.SplitData.node1543 := by
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
  · exact treeEq1544

def B1547 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq1547 : B1547.tree = HexagonCover.NBand.M6900_7100.SplitData.node1547 := by
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

def B1546 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1547, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1546 : B1546.tree = HexagonCover.NBand.M6900_7100.SplitData.node1546 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1547
  · rfl
  · rfl

def B1542 : Block := .branch 124 ![748288838313422309697177209955810087465685155316097, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![B1543, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1546]
theorem treeEq1542 : B1542.tree = HexagonCover.NBand.M6900_7100.SplitData.node1542 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1543
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1546

def B1532 : Block := .branch 119 ![748288838313422309697177209955810087465685155316097, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1533, (.leaf 5 (Common.fact 163).pointIds 163), B1542]
theorem treeEq1532 : B1532.tree = HexagonCover.NBand.M6900_7100.SplitData.node1532 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1533
  · rfl
  · exact treeEq1542

def B1549 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq1549 : B1549.tree = HexagonCover.NBand.M6900_7100.SplitData.node1549 := by
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

def B1548 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1549, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1548 : B1548.tree = HexagonCover.NBand.M6900_7100.SplitData.node1548 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1549
  · rfl
  · rfl

def B1531 : Block := .branch 112 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1532, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B1548]
theorem treeEq1531 : B1531.tree = HexagonCover.NBand.M6900_7100.SplitData.node1531 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1548

theorem accepted1531 : B1531.accepted = true := by decide +kernel
theorem checked1531 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1531 (maskNeeds ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024]) := by
  rw [← treeEq1531]
  exact B1531.sound accepted1531
#print axioms checked1531

def Tip1515_1531 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1531 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] checked1531
def B1526 : Block := .branch 124 ![94266855607843238224137671710200254767807649022337, 1538, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1526 : B1526.tree = HexagonCover.NBand.M6900_7100.SplitData.node1526 := by
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

def B1525 : Block := .branch 159 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![B1526, (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1525 : B1525.tree = HexagonCover.NBand.M6900_7100.SplitData.node1525 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1526
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1524 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), B1525, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1524 : B1524.tree = HexagonCover.NBand.M6900_7100.SplitData.node1524 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1525
  · rfl
  · rfl
  · rfl
  · rfl

def B1523 : Block := .branch 161 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38690348594151003235835912, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1524, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq1523 : B1523.tree = HexagonCover.NBand.M6900_7100.SplitData.node1523 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1524
  · rfl
  · rfl
  · rfl
  · rfl

def B1522 : Block := .branch 137 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1523, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1522 : B1522.tree = HexagonCover.NBand.M6900_7100.SplitData.node1522 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1523
  · rfl
  · rfl
  · rfl

def B1521 : Block := .branch 162 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1522, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 745).pointIds 745)]
theorem treeEq1521 : B1521.tree = HexagonCover.NBand.M6900_7100.SplitData.node1521 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1522
  · rfl
  · rfl

def B1520 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 498).pointIds 498), B1521]
theorem treeEq1520 : B1520.tree = HexagonCover.NBand.M6900_7100.SplitData.node1520 := by
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
  · exact treeEq1521

def B1519 : Block := .branch 166 ![385, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144419178489219192437863107007534568305279369280] ![B1520, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1519 : B1519.tree = HexagonCover.NBand.M6900_7100.SplitData.node1519 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1520
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1518 : Block := .branch 151 ![385, 906694436769665430586882, 6148, 38690348594151003235835912, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 662).pointIds 662), B1519, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1518 : B1518.tree = HexagonCover.NBand.M6900_7100.SplitData.node1518 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1519
  · rfl

def B1530 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1530 : B1530.tree = HexagonCover.NBand.M6900_7100.SplitData.node1530 := by
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

def B1529 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1530, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1529 : B1529.tree = HexagonCover.NBand.M6900_7100.SplitData.node1529 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1530
  · rfl
  · rfl

def B1528 : Block := .branch 124 ![10384594955009694542441267557564801, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1529]
theorem treeEq1528 : B1528.tree = HexagonCover.NBand.M6900_7100.SplitData.node1528 := by
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
  · exact treeEq1529

def B1527 : Block := .branch 90 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1528, Tip1515_1531, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1527 : B1527.tree = HexagonCover.NBand.M6900_7100.SplitData.node1527 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1528
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1517 : Block := .branch 108 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B1518, (.leaf 5 (Common.fact 322).pointIds 322), B1527]
theorem treeEq1517 : B1517.tree = HexagonCover.NBand.M6900_7100.SplitData.node1517 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1518
  · rfl
  · exact treeEq1527

def B1551 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 682).pointIds 682)]
theorem treeEq1551 : B1551.tree = HexagonCover.NBand.M6900_7100.SplitData.node1551 := by
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

def B1550 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1551, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 681).pointIds 681)]
theorem treeEq1550 : B1550.tree = HexagonCover.NBand.M6900_7100.SplitData.node1550 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1551
  · rfl
  · rfl

def B1516 : Block := .branch 89 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 104).pointIds 104), B1517, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B1550]
theorem treeEq1516 : B1516.tree = HexagonCover.NBand.M6900_7100.SplitData.node1516 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1517
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1550

def B1553 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1553 : B1553.tree = HexagonCover.NBand.M6900_7100.SplitData.node1553 := by
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

def B1552 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1553, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1552 : B1552.tree = HexagonCover.NBand.M6900_7100.SplitData.node1552 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1553
  · rfl
  · rfl

def B1515 : Block := .branch 86 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B1516, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B1552]
theorem treeEq1515 : B1515.tree = HexagonCover.NBand.M6900_7100.SplitData.node1515 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1516
  · rfl
  · rfl
  · exact treeEq1552

theorem accepted1515 : B1515.accepted = true := by decide +kernel
theorem checked1515 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1515 (maskNeeds ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280]) := by
  rw [← treeEq1515]
  exact B1515.sound accepted1515
#print axioms checked1515

def B1595 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1595 : B1595.tree = HexagonCover.NBand.M6900_7100.SplitData.node1595 := by
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

def B1594 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![B1595, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1594 : B1594.tree = HexagonCover.NBand.M6900_7100.SplitData.node1594 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1595
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1593 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B1594, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1593 : B1593.tree = HexagonCover.NBand.M6900_7100.SplitData.node1593 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1594
  · rfl
  · rfl
  · rfl
  · rfl

def B1592 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38690348594151003235835912, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1593, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1592 : B1592.tree = HexagonCover.NBand.M6900_7100.SplitData.node1592 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1593
  · rfl
  · rfl
  · rfl
  · rfl

def B1591 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1592, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1591 : B1591.tree = HexagonCover.NBand.M6900_7100.SplitData.node1591 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1592
  · rfl
  · rfl
  · rfl

def B1590 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1591, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1590 : B1590.tree = HexagonCover.NBand.M6900_7100.SplitData.node1590 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1591
  · rfl
  · rfl

def B1589 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1590]
theorem treeEq1589 : B1589.tree = HexagonCover.NBand.M6900_7100.SplitData.node1589 := by
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
  · exact treeEq1590

def B1588 : Block := .branch 166 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309448580807785149258793024] ![B1589, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1588 : B1588.tree = HexagonCover.NBand.M6900_7100.SplitData.node1588 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1589
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1587 : Block := .branch 151 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1588, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1587 : B1587.tree = HexagonCover.NBand.M6900_7100.SplitData.node1587 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1588
  · rfl

def B1599 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1599 : B1599.tree = HexagonCover.NBand.M6900_7100.SplitData.node1599 := by
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

def B1598 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1599, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1598 : B1598.tree = HexagonCover.NBand.M6900_7100.SplitData.node1598 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1599
  · rfl
  · rfl

def B1597 : Block := .branch 159 ![748288838313443577345109768609186252568290935177601, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1598]
theorem treeEq1597 : B1597.tree = HexagonCover.NBand.M6900_7100.SplitData.node1597 := by
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
  · exact treeEq1598

def B1601 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq1601 : B1601.tree = HexagonCover.NBand.M6900_7100.SplitData.node1601 := by
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

def B1600 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1601, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1600 : B1600.tree = HexagonCover.NBand.M6900_7100.SplitData.node1600 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1601
  · rfl
  · rfl

def B1596 : Block := .branch 124 ![748288838313422309697177209955219791655326449664385, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![B1597, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1600]
theorem treeEq1596 : B1596.tree = HexagonCover.NBand.M6900_7100.SplitData.node1596 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1597
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1600

def B1586 : Block := .branch 119 ![748288838313422309697177209955219791655326449664385, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1587, (.leaf 5 (Common.fact 163).pointIds 163), B1596]
theorem treeEq1586 : B1586.tree = HexagonCover.NBand.M6900_7100.SplitData.node1586 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1587
  · rfl
  · exact treeEq1596

def B1603 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq1603 : B1603.tree = HexagonCover.NBand.M6900_7100.SplitData.node1603 := by
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

def B1602 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1603, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1602 : B1602.tree = HexagonCover.NBand.M6900_7100.SplitData.node1602 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1603
  · rfl
  · rfl

def B1585 : Block := .branch 112 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1586, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B1602]
theorem treeEq1585 : B1585.tree = HexagonCover.NBand.M6900_7100.SplitData.node1585 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1586
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1602

theorem accepted1585 : B1585.accepted = true := by decide +kernel
theorem checked1585 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1585 (maskNeeds ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024]) := by
  rw [← treeEq1585]
  exact B1585.sound accepted1585
#print axioms checked1585

end HexagonCover.NBand.M6900_7100.SplitTree.Run0019
