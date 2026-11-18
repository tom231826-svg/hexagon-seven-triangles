import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0011
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0012
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0894_0896 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0896 ![10384593717069655257060992658440577, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0011.checked0896
def B0978 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0978 : B0978.tree = HexagonCover.NBand.M6900_7100.SplitData.node0978 := by
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

def B0977 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0978, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0977 : B0977.tree = HexagonCover.NBand.M6900_7100.SplitData.node0977 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0978
  · rfl
  · rfl

def B0976 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218543403231594674788036628713046080] ![B0977, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0976 : B0976.tree = HexagonCover.NBand.M6900_7100.SplitData.node0976 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0977
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0975 : Block := .branch 151 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0976, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0975 : B0975.tree = HexagonCover.NBand.M6900_7100.SplitData.node0975 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0976
  · rfl

def B0974 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0975, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0974 : B0974.tree = HexagonCover.NBand.M6900_7100.SplitData.node0974 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0975
  · rfl
  · rfl

def B0895 : Block := .branch 91 ![10384593717069655257060992658440577, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip0894_0896, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B0974]
theorem treeEq0895 : B0895.tree = HexagonCover.NBand.M6900_7100.SplitData.node0895 := by
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
  · exact treeEq0974

def B0988 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468372414128216807114477103961150943789088, 385836432277136441889030543861336302778395099922496] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 736).pointIds 736), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0988 : B0988.tree = HexagonCover.NBand.M6900_7100.SplitData.node0988 := by
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

def B0987 : Block := .branch 125 ![841824943102600080885322463644579019321817144754561, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0988, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0987 : B0987.tree = HexagonCover.NBand.M6900_7100.SplitData.node0987 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0988
  · rfl

def B0986 : Block := .branch 169 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![B0987, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq0986 : B0986.tree = HexagonCover.NBand.M6900_7100.SplitData.node0986 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0987
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0985 : Block := .branch 163 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 233843116468329878832351689806544182135221972762656, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B0986]
theorem treeEq0985 : B0985.tree = HexagonCover.NBand.M6900_7100.SplitData.node0985 := by
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
  · exact treeEq0986

def B0984 : Block := .branch 165 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 187075064073740985449833775159623125506232131387424, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B0985, (.leaf 0 [] 0)]
theorem treeEq0984 : B0984.tree = HexagonCover.NBand.M6900_7100.SplitData.node0984 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0985
  · rfl

def B0983 : Block := .branch 167 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B0984, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0983 : B0983.tree = HexagonCover.NBand.M6900_7100.SplitData.node0983 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0984
  · rfl

def B0982 : Block := .branch 142 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0983, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq0982 : B0982.tree = HexagonCover.NBand.M6900_7100.SplitData.node0982 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0983
  · rfl
  · rfl

def B0981 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![B0982, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0981 : B0981.tree = HexagonCover.NBand.M6900_7100.SplitData.node0981 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0982
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0980 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0981, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0980 : B0980.tree = HexagonCover.NBand.M6900_7100.SplitData.node0980 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0981
  · rfl

def B0979 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0980, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq0979 : B0979.tree = HexagonCover.NBand.M6900_7100.SplitData.node0979 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0980
  · rfl
  · rfl

def B0894 : Block := .branch 89 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), B0895, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0979]
theorem treeEq0894 : B0894.tree = HexagonCover.NBand.M6900_7100.SplitData.node0894 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0895
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0979

theorem accepted0894 : B0894.accepted = true := by decide +kernel
theorem checked0894 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0894 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0894]
  exact B0894.sound accepted0894
#print axioms checked0894

def B1045 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1045 : B1045.tree = HexagonCover.NBand.M6900_7100.SplitData.node1045 := by
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

def B1044 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![B1045, (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1044 : B1044.tree = HexagonCover.NBand.M6900_7100.SplitData.node1044 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1045
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1043 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), B1044, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1043 : B1043.tree = HexagonCover.NBand.M6900_7100.SplitData.node1043 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1044
  · rfl
  · rfl
  · rfl
  · rfl

def B1042 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38695070960633872881049608, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1043, (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1042 : B1042.tree = HexagonCover.NBand.M6900_7100.SplitData.node1042 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1043
  · rfl
  · rfl
  · rfl
  · rfl

def B1041 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38695070960633872881049608, 5847433797016317632695797616834581573760113016848, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1042, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1041 : B1041.tree = HexagonCover.NBand.M6900_7100.SplitData.node1041 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1042
  · rfl
  · rfl
  · rfl

def B1040 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B1041, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1040 : B1040.tree = HexagonCover.NBand.M6900_7100.SplitData.node1040 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1041
  · rfl
  · rfl

def B1039 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1040]
theorem treeEq1039 : B1039.tree = HexagonCover.NBand.M6900_7100.SplitData.node1039 := by
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
  · exact treeEq1040

def B1038 : Block := .branch 166 ![5192296858534827628530496329220481, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309448580807785149258793024] ![B1039, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1038 : B1038.tree = HexagonCover.NBand.M6900_7100.SplitData.node1038 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1039
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1037 : Block := .branch 151 ![5192296858534827628530496329220481, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1038, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1037 : B1037.tree = HexagonCover.NBand.M6900_7100.SplitData.node1037 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1038
  · rfl

def B1049 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1049 : B1049.tree = HexagonCover.NBand.M6900_7100.SplitData.node1049 := by
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

def B1048 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1049, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1048 : B1048.tree = HexagonCover.NBand.M6900_7100.SplitData.node1048 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1049
  · rfl
  · rfl

def B1047 : Block := .branch 159 ![748288838313443577345109768609776548378649640829313, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1048]
theorem treeEq1047 : B1047.tree = HexagonCover.NBand.M6900_7100.SplitData.node1047 := by
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
  · exact treeEq1048

def B1051 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq1051 : B1051.tree = HexagonCover.NBand.M6900_7100.SplitData.node1051 := by
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

def B1050 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1051, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1050 : B1050.tree = HexagonCover.NBand.M6900_7100.SplitData.node1050 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1051
  · rfl
  · rfl

def B1046 : Block := .branch 124 ![748288838313422309697177209955810087465685155316097, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![B1047, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1050]
theorem treeEq1046 : B1046.tree = HexagonCover.NBand.M6900_7100.SplitData.node1046 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1047
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1050

def B1036 : Block := .branch 119 ![748288838313422309697177209955810087465685155316097, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1037, (.leaf 5 (Common.fact 163).pointIds 163), B1046]
theorem treeEq1036 : B1036.tree = HexagonCover.NBand.M6900_7100.SplitData.node1036 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1037
  · rfl
  · exact treeEq1046

def B1053 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq1053 : B1053.tree = HexagonCover.NBand.M6900_7100.SplitData.node1053 := by
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

def B1052 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1053, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1052 : B1052.tree = HexagonCover.NBand.M6900_7100.SplitData.node1052 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1053
  · rfl
  · rfl

def B1035 : Block := .branch 112 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1036, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B1052]
theorem treeEq1035 : B1035.tree = HexagonCover.NBand.M6900_7100.SplitData.node1035 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1036
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1052

theorem accepted1035 : B1035.accepted = true := by decide +kernel
theorem checked1035 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1035 (maskNeeds ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024]) := by
  rw [← treeEq1035]
  exact B1035.sound accepted1035
#print axioms checked1035

def Tip1019_1035 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1035 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] checked1035
def B1030 : Block := .branch 124 ![94266855607843238224137671710200254767807649022337, 1538, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1030 : B1030.tree = HexagonCover.NBand.M6900_7100.SplitData.node1030 := by
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

def B1029 : Block := .branch 159 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![B1030, (.leaf 1 (Common.fact 666).pointIds 666), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1029 : B1029.tree = HexagonCover.NBand.M6900_7100.SplitData.node1029 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1030
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1028 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 24584, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), B1029, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1028 : B1028.tree = HexagonCover.NBand.M6900_7100.SplitData.node1028 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1029
  · rfl
  · rfl
  · rfl
  · rfl

def B1027 : Block := .branch 161 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38695070960633872881049608, 98320, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1028, (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq1027 : B1027.tree = HexagonCover.NBand.M6900_7100.SplitData.node1027 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1028
  · rfl
  · rfl
  · rfl
  · rfl

def B1026 : Block := .branch 137 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38695070960633872881049608, 5847433797016317632695797616834581573760113016848, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1027, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1026 : B1026.tree = HexagonCover.NBand.M6900_7100.SplitData.node1026 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1027
  · rfl
  · rfl
  · rfl

def B1025 : Block := .branch 162 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 11172150671397605652471983485842964214186048] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B1026, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 745).pointIds 745)]
theorem treeEq1025 : B1025.tree = HexagonCover.NBand.M6900_7100.SplitData.node1025 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1026
  · rfl
  · rfl

def B1024 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 498).pointIds 498), B1025]
theorem treeEq1024 : B1024.tree = HexagonCover.NBand.M6900_7100.SplitData.node1024 := by
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
  · exact treeEq1025

def B1023 : Block := .branch 166 ![385, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144419178489219192437863107007534568305279369280] ![B1024, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1023 : B1023.tree = HexagonCover.NBand.M6900_7100.SplitData.node1023 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1024
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1022 : Block := .branch 151 ![385, 906694436769665430586882, 6148, 38695070960633872881049608, 1427247692706284399611944396176278292403421200, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 662).pointIds 662), B1023, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1022 : B1022.tree = HexagonCover.NBand.M6900_7100.SplitData.node1022 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1023
  · rfl

def B1034 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1034 : B1034.tree = HexagonCover.NBand.M6900_7100.SplitData.node1034 := by
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

def B1033 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21799339455391174049607026298217750331456] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1034, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1033 : B1033.tree = HexagonCover.NBand.M6900_7100.SplitData.node1033 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1034
  · rfl
  · rfl

def B1032 : Block := .branch 124 ![10384594955009694542441267557564801, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1033]
theorem treeEq1032 : B1032.tree = HexagonCover.NBand.M6900_7100.SplitData.node1032 := by
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
  · exact treeEq1033

def B1031 : Block := .branch 90 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1032, Tip1019_1035, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1031 : B1031.tree = HexagonCover.NBand.M6900_7100.SplitData.node1031 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1032
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1021 : Block := .branch 108 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B1022, (.leaf 5 (Common.fact 322).pointIds 322), B1031]
theorem treeEq1021 : B1021.tree = HexagonCover.NBand.M6900_7100.SplitData.node1021 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1022
  · rfl
  · exact treeEq1031

def B1055 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 682).pointIds 682)]
theorem treeEq1055 : B1055.tree = HexagonCover.NBand.M6900_7100.SplitData.node1055 := by
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

def B1054 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072132294700674143992208920910757952] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1055, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 681).pointIds 681)]
theorem treeEq1054 : B1054.tree = HexagonCover.NBand.M6900_7100.SplitData.node1054 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1055
  · rfl
  · rfl

def B1020 : Block := .branch 89 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 104).pointIds 104), B1021, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B1054]
theorem treeEq1020 : B1020.tree = HexagonCover.NBand.M6900_7100.SplitData.node1020 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1021
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1054

def B1057 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1057 : B1057.tree = HexagonCover.NBand.M6900_7100.SplitData.node1057 := by
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

def B1056 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072131977246425319747504676466589760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1057, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1056 : B1056.tree = HexagonCover.NBand.M6900_7100.SplitData.node1056 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1057
  · rfl
  · rfl

def B1019 : Block := .branch 86 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B1020, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B1056]
theorem treeEq1019 : B1019.tree = HexagonCover.NBand.M6900_7100.SplitData.node1019 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1020
  · rfl
  · rfl
  · exact treeEq1056

theorem accepted1019 : B1019.accepted = true := by decide +kernel
theorem checked1019 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1019 (maskNeeds ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280]) := by
  rw [← treeEq1019]
  exact B1019.sound accepted1019
#print axioms checked1019

def B1099 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 672).pointIds 672)]
theorem treeEq1099 : B1099.tree = HexagonCover.NBand.M6900_7100.SplitData.node1099 := by
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

def B1098 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![B1099, (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1098 : B1098.tree = HexagonCover.NBand.M6900_7100.SplitData.node1098 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1099
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1097 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 24584, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), B1098, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1097 : B1097.tree = HexagonCover.NBand.M6900_7100.SplitData.node1097 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1098
  · rfl
  · rfl
  · rfl
  · rfl

def B1096 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38695070960633872881049608, 98320, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1097, (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1096 : B1096.tree = HexagonCover.NBand.M6900_7100.SplitData.node1096 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1097
  · rfl
  · rfl
  · rfl
  · rfl

def B1095 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38695070960633872881049608, 5847433797016317632695797616834581573760113016848, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1096, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1095 : B1095.tree = HexagonCover.NBand.M6900_7100.SplitData.node1095 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1096
  · rfl
  · rfl
  · rfl

def B1094 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 11172150671072770186163499701709434017808448] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B1095, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1094 : B1094.tree = HexagonCover.NBand.M6900_7100.SplitData.node1094 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1095
  · rfl
  · rfl

def B1093 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 737941821641931621890, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1094]
theorem treeEq1093 : B1093.tree = HexagonCover.NBand.M6900_7100.SplitData.node1093 := by
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
  · exact treeEq1094

def B1092 : Block := .branch 166 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309448580807785149258793024] ![B1093, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1092 : B1092.tree = HexagonCover.NBand.M6900_7100.SplitData.node1092 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1093
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1091 : Block := .branch 151 ![5192296858534827628530496329220481, 737941821641931621890, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1092, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1091 : B1091.tree = HexagonCover.NBand.M6900_7100.SplitData.node1091 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1092
  · rfl

def B1103 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1103 : B1103.tree = HexagonCover.NBand.M6900_7100.SplitData.node1103 := by
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

def B1102 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 730750840444187556039796611508432015455350685760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1103, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1102 : B1102.tree = HexagonCover.NBand.M6900_7100.SplitData.node1102 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1103
  · rfl
  · rfl

def B1101 : Block := .branch 159 ![748288838313443577345109768609186252568290935177601, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 690).pointIds 690), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1102]
theorem treeEq1101 : B1101.tree = HexagonCover.NBand.M6900_7100.SplitData.node1101 := by
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
  · exact treeEq1102

def B1105 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq1105 : B1105.tree = HexagonCover.NBand.M6900_7100.SplitData.node1105 := by
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

def B1104 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21800003744870512849116751418591869927488] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1105, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1104 : B1104.tree = HexagonCover.NBand.M6900_7100.SplitData.node1104 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1105
  · rfl
  · rfl

def B1100 : Block := .branch 124 ![748288838313422309697177209955219791655326449664385, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778736096937954195150290505627384414272] ![B1101, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1104]
theorem treeEq1100 : B1100.tree = HexagonCover.NBand.M6900_7100.SplitData.node1100 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1101
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1104

def B1090 : Block := .branch 119 ![748288838313422309697177209955219791655326449664385, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1091, (.leaf 5 (Common.fact 163).pointIds 163), B1100]
theorem treeEq1090 : B1090.tree = HexagonCover.NBand.M6900_7100.SplitData.node1090 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1091
  · rfl
  · exact treeEq1100

def B1107 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 680).pointIds 680)]
theorem treeEq1107 : B1107.tree = HexagonCover.NBand.M6900_7100.SplitData.node1107 := by
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

def B1106 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778076999755473930468193915749594038336] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B1107, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1106 : B1106.tree = HexagonCover.NBand.M6900_7100.SplitData.node1106 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1107
  · rfl
  · rfl

def B1089 : Block := .branch 112 ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024] ![B1090, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B1106]
theorem treeEq1089 : B1089.tree = HexagonCover.NBand.M6900_7100.SplitData.node1089 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1090
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1106

theorem accepted1089 : B1089.accepted = true := by decide +kernel
theorem checked1089 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1089 (maskNeeds ![748288838313422304504880351420392163124830120444289, 1033089726821284447746, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309448580807785149258793024]) := by
  rw [← treeEq1089]
  exact B1089.sound accepted1089
#print axioms checked1089

end HexagonCover.NBand.M6900_7100.SplitTree.Run0012
