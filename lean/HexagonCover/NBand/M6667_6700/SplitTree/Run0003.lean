import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0001
import HexagonCover.NBand.M6667_6700.SplitTree.Run0002
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0146_0160 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0160 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 158533696280984011454269120520, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] HexagonCover.NBand.M6667_6700.SplitTree.Run0001.checked0160
def B0180 : Block := .branch 170 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168693052279698165097972649951296] ![(.leaf 0 (Common.fact 484).pointIds 484), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 488).pointIds 488), (.leaf 5 (Common.fact 489).pointIds 489), (.leaf 6 (Common.fact 520).pointIds 520)]
theorem treeEq0180 : B0180.tree = HexagonCover.NBand.M6667_6700.SplitData.node0180 := by
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

def B0159 : Block := .branch 97 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 92060263772684228656152136994276517341875798048, 374144419167940465168534595954669636422785562050624] ![(.leaf 0 (Common.fact 462).pointIds 462), (.leaf 1 (Common.fact 463).pointIds 463), (.leaf 2 (Common.fact 464).pointIds 464), Tip0146_0160, (.leaf 4 (Common.fact 465).pointIds 465), (.leaf 5 (Common.fact 466).pointIds 466), B0180]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M6667_6700.SplitData.node0159 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0180

def B0158 : Block := .branch 149 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 91346639926331248715622994009551769773684424736, 374144419167940466791761189546917385039314016534592] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), (.leaf 4 (Common.fact 460).pointIds 460), B0159, (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M6667_6700.SplitData.node0158 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0159
  · rfl

def B0157 : Block := .branch 156 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 2787593149816327892691964784081045188640800, 374144419167940466791761189546917385039314016534592] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 459).pointIds 459), B0158, (.leaf 0 [] 0)]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M6667_6700.SplitData.node0157 := by
  change Tree.branch (156 : Fin 173) _ = Tree.branch (156 : Fin 173) _
  apply congrArg (Tree.branch (156 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0158
  · rfl

def B0156 : Block := .branch 164 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 2787593149816327892691964784081045188640800, 374144419167940466791761189546917385039314016534592] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 458).pointIds 458), B0157, (.leaf 0 [] 0)]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M6667_6700.SplitData.node0156 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0157
  · rfl

def B0155 : Block := .branch 166 ![63805539946105229314349925646227997057, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 2787593149816327892691964784081045188640800, 374144419167940466791761189546917385039314016534592] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 457).pointIds 457), B0156, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M6667_6700.SplitData.node0155 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0156
  · rfl

def B0154 : Block := .branch 125 ![21270244080987921381428099717256970625, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 187072212365948723346399551279649010597004554141728, 374144419167940466791761189546917385039314016534592] ![B0155, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 456).pointIds 456)]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M6667_6700.SplitData.node0154 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0155
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0153 : Block := .branch 158 ![21270244080987921381428099717256970625, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 187072212365948723346399551279649010597004554141728, 374144419167941131405759082004853836942844156706880] ![(.leaf 0 (Common.fact 454).pointIds 454), B0154, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M6667_6700.SplitData.node0153 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0154
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0152 : Block := .branch 124 ![2596148429267414967186752771457409, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 187072212365948723346399551279649010597004554141728, 374144419167941131405759082004853836942844156706880] ![B0153, (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 450).pointIds 450), (.leaf 4 (Common.fact 451).pointIds 451), (.leaf 5 (Common.fact 452).pointIds 452), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M6667_6700.SplitData.node0152 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0153
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0151 : Block := .branch 141 ![2596148429267414967186752771457409, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 187072209578355573530071658587684226515959365894176, 374144419167941131405759082004853836942844156706880] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 446).pointIds 446), B0152, (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M6667_6700.SplitData.node0151 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0152
  · rfl

def B0150 : Block := .branch 165 ![2596148429267414967186752771457409, 1099511629314, 77919046967349146032132, 77371252455336267181219848, 748288838313424952576278204182482713677958022791184, 187072209578355573530071658587684226515959365894176, 374144419167941131405759082004853836942844156706880] ![B0151, (.leaf 1 (Common.fact 440).pointIds 440), (.leaf 2 (Common.fact 441).pointIds 441), (.leaf 3 (Common.fact 442).pointIds 442), (.leaf 4 (Common.fact 443).pointIds 443), (.leaf 5 (Common.fact 444).pointIds 444), (.leaf 6 (Common.fact 445).pointIds 445)]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M6667_6700.SplitData.node0150 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0151
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0149 : Block := .branch 128 ![2596148429267414967186752771457409, 1099511629314, 77919046967349146032132, 96714065569170333976518664, 748288838313424952576278204182482713677958022791184, 187072209578355573530071658587684226515959365894176, 374144419167600849038838143541390462335412388495424] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 438).pointIds 438), (.leaf 5 (Common.fact 439).pointIds 439), B0150]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M6667_6700.SplitData.node0149 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0150

def B0148 : Block := .branch 169 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 2658455991569831745807614120560787472, 187072209578355573530071658587684226515959365894176, 374144419167600849038838143541390462335412388495424] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0149, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 433).pointIds 433)]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M6667_6700.SplitData.node0148 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0149
  · rfl
  · rfl

def B0147 : Block := .branch 133 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 2658455991569831745807614120560787472, 187072209578355573530071658587684226515959365894176, 374144419156711813297368112710562474897595805728832] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), B0148]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M6667_6700.SplitData.node0147 := by
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
  · exact treeEq0148

def B0146 : Block := .branch 167 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 2658455991569831745807614120560787472, 393248, 374144419156711813297368112710562474897595805728832] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 431).pointIds 431), B0147, (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M6667_6700.SplitData.node0146 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0147
  · rfl

theorem accepted0146 : B0146.accepted = true := by decide +kernel
theorem checked0146 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0146 (maskNeeds ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 2658455991569831745807614120560787472, 393248, 374144419156711813297368112710562474897595805728832]) := by
  rw [← treeEq0146]
  exact B0146.sound accepted0146
#print axioms checked0146

def Tip0142_0185 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0185 ![15953334633149458346271674469542003073, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21778071482940061661655974875633165926432, 385836432255359036642997746114797649727377628463168] HexagonCover.NBand.M6667_6700.SplitTree.Run0002.checked0185
def Tip0142_0264 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0264 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 174224571863520493293247799005065324363792, 21778071482940061661655974875633165926432, 374144419156719788665342822205799897739957487796288] HexagonCover.NBand.M6667_6700.SplitTree.Run0002.checked0264
def Tip0142_0146 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0146 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 2658455991569831745807614120560787472, 393248, 374144419156711813297368112710562474897595805728832] checked0146
def B0144 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 1122433257470134105795061978769165747045653164851264] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M6667_6700.SplitData.node0144 := by
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

def B0143 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329227995784915872903807060280442896, 393248, 374144419156711811674775344418428840981815702847552] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B0144]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M6667_6700.SplitData.node0143 := by
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
  · exact treeEq0144

def B0263 : Block := .branch 172 ![5319508131568930906582414993892835713, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 748288838313422294120286634350736906063837462102032, 91349427519481065043515685974335850818872672288, 3367299772410751239732177381853772503696801070055488] ![(.leaf 0 (Common.fact 623).pointIds 623), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 625).pointIds 625), (.leaf 6 (Common.fact 626).pointIds 626)]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M6667_6700.SplitData.node0263 := by
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
  · rfl

def B0262 : Block := .branch 128 ![5319508131568930906582414993892835713, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 91349427519481065043515685974335850818872672288, 3367299772410410957365256443390309129089369301844032] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), B0263]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M6667_6700.SplitData.node0262 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0263

def B0261 : Block := .branch 142 ![5319508131568930906582414993892835713, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 91343852333181432387730302044767688728496177184, 3367299772410410958988483036982556877705897756328000] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 549).pointIds 549), B0262, (.leaf 6 (Common.fact 550).pointIds 550)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M6667_6700.SplitData.node0261 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0262
  · rfl

def B0260 : Block := .branch 150 ![5319508131568930906582414993892835713, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 91343852333181432387730302044767688728496177184, 3367299772410410958988483191725061788378432118718528] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 547).pointIds 547), B0261, (.leaf 6 (Common.fact 548).pointIds 548)]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M6667_6700.SplitData.node0260 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0261
  · rfl

def B0259 : Block := .branch 156 ![5319508131568930906582414993892835713, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 393248, 3367299772410410958988483191725061788378432118718528] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 546).pointIds 546), B0260, (.leaf 0 [] 0)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M6667_6700.SplitData.node0259 := by
  change Tree.branch (156 : Fin 173) _ = Tree.branch (156 : Fin 173) _
  apply congrArg (Tree.branch (156 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0260
  · rfl

def B0258 : Block := .branch 164 ![5319508131568930906582414993892835713, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 393248, 3367299772410410958988483191725061788378432118718528] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 545).pointIds 545), B0259, (.leaf 0 [] 0)]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M6667_6700.SplitData.node0258 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0259
  · rfl

def B0257 : Block := .branch 166 ![5319508131568930906582414993892835713, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 393248, 3367299772410410958988483191725061788378432118718528] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 544).pointIds 544), B0258, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M6667_6700.SplitData.node0257 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0258
  · rfl

def B0256 : Block := .branch 158 ![5319508131568930906582414993892835713, 1099511629314, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 393248, 3367299772410410958988483191725061788378432118718528] ![(.leaf 0 (Common.fact 542).pointIds 542), B0257, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M6667_6700.SplitData.node0256 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0257
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0255 : Block := .branch 171 ![5319508131568930906582414993892835713, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 21778071482940061661655974875633165926432, 374144419156721782507336654322114164123082270703680] ![(.leaf 0 (Common.fact 537).pointIds 537), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 541).pointIds 541), B0256]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M6667_6700.SplitData.node0255 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0256

def B0254 : Block := .branch 169 ![5319510666870131363041217987299246465, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 374144419156722447121334546780050616026612410875968] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0255, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 620).pointIds 620)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M6667_6700.SplitData.node0254 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0255
  · rfl
  · rfl

def B0184 : Block := .branch 123 ![5319510666870131363041217987299246465, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21778071482940061661655974875633165926432, 385836432255359036642997746114797649727377628463168] ![Tip0142_0185, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0254]
theorem treeEq0184 : B0184.tree = HexagonCover.NBand.M6667_6700.SplitData.node0184 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0254

def B0183 : Block := .branch 140 ![5319510666870131363041217987299246465, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 385836432255361695098989315946543457341498189152320] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0184, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0183 : B0183.tree = HexagonCover.NBand.M6667_6700.SplitData.node0183 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0184
  · rfl
  · rfl

def B0182 : Block := .branch 163 ![5319510666870131363041217987299246465, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156714471753359837284813193184250728808512] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B0183]
theorem treeEq0182 : B0182.tree = HexagonCover.NBand.M6667_6700.SplitData.node0182 := by
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
  · exact treeEq0183

def B0181 : Block := .branch 122 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156714471753359837284813193184250728808512] ![B0182, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip0142_0264]
theorem treeEq0181 : B0181.tree = HexagonCover.NBand.M6667_6700.SplitData.node0181 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0182
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0145 : Block := .branch 121 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711813297368267453067385570130168119360] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), Tip0142_0146, (.leaf 5 (Common.fact 430).pointIds 430), B0181]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M6667_6700.SplitData.node0145 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0181

def B0142 : Block := .branch 120 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711813297368267453067385570130168119360] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B0143, (.leaf 5 (Common.fact 163).pointIds 163), B0145]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M6667_6700.SplitData.node0142 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0143
  · rfl
  · exact treeEq0145

theorem accepted0142 : B0142.accepted = true := by decide +kernel
theorem checked0142 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0142 (maskNeeds ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711813297368267453067385570130168119360]) := by
  rw [← treeEq0142]
  exact B0142.sound accepted0142
#print axioms checked0142

def B0301 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M6667_6700.SplitData.node0301 := by
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

def B0300 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B0301]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M6667_6700.SplitData.node0300 := by
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
  · exact treeEq0301

def B0304 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M6667_6700.SplitData.node0304 := by
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

def B0303 : Block := .branch 171 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 2658455991569831745807614120560787472, 21778071482940061661655974875633165926432, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 666).pointIds 666), (.leaf 1 (Common.fact 667).pointIds 667), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 541).pointIds 541), B0304]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M6667_6700.SplitData.node0303 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0304

def B0310 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M6667_6700.SplitData.node0310 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0309 : Block := .branch 171 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 666).pointIds 666), (.leaf 1 (Common.fact 667).pointIds 667), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), B0310, (.leaf 5 (Common.fact 541).pointIds 541), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M6667_6700.SplitData.node0309 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0310
  · rfl
  · rfl

def B0308 : Block := .branch 158 ![5319510666870131363041217987299246465, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0309]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M6667_6700.SplitData.node0308 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0309

def B0307 : Block := .branch 140 ![5319510666870131363041217987299246465, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 98320, 21778071482940061661655974875633165926432, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0308, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M6667_6700.SplitData.node0307 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0308
  · rfl
  · rfl

def B0306 : Block := .branch 163 ![5319510666870131363041217987299246465, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 98320, 21778071482940061661655974875633165926432, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B0307]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M6667_6700.SplitData.node0306 := by
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
  · exact treeEq0307

def B0315 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M6667_6700.SplitData.node0315 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0314 : Block := .branch 171 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 666).pointIds 666), (.leaf 1 (Common.fact 667).pointIds 667), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), B0315, (.leaf 5 (Common.fact 541).pointIds 541), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M6667_6700.SplitData.node0314 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0315
  · rfl
  · rfl

def B0313 : Block := .branch 158 ![10636422650009794854656446228420624769, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0314]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M6667_6700.SplitData.node0313 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0314

def B0318 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M6667_6700.SplitData.node0318 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0317 : Block := .branch 171 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 21778071482940061661655974875633165926432, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 666).pointIds 666), (.leaf 1 (Common.fact 667).pointIds 667), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 541).pointIds 541), B0318]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M6667_6700.SplitData.node0317 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0318

def B0316 : Block := .branch 169 ![2535301200457611724498013258113, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0317, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M6667_6700.SplitData.node0316 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0317
  · rfl
  · rfl

def B0312 : Block := .branch 123 ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6360455125664098140004408993934437576289060004560960] ![B0313, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0316]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M6667_6700.SplitData.node0312 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0313
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0316

def B0311 : Block := .branch 140 ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0312, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M6667_6700.SplitData.node0311 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0312
  · rfl
  · rfl

def B0305 : Block := .branch 122 ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664092823093059679571060075761567234785344] ![B0306, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B0311]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M6667_6700.SplitData.node0305 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0306
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0311

def B0302 : Block := .branch 121 ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B0303, (.leaf 5 (Common.fact 430).pointIds 430), B0305]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M6667_6700.SplitData.node0302 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0303
  · rfl
  · exact treeEq0305

def B0299 : Block := .branch 120 ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B0300, (.leaf 5 (Common.fact 163).pointIds 163), B0302]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M6667_6700.SplitData.node0299 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0300
  · rfl
  · exact treeEq0302

theorem accepted0299 : B0299.accepted = true := by decide +kernel
theorem checked0299 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0299 (maskNeeds ![2598683730467871425989746177868161, 618970609938501595666843138, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664090165935142324373021175280070756401216]) := by
  rw [← treeEq0299]
  exact B0299.sound accepted0299
#print axioms checked0299

def Tip0138_0142 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0142 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711813297368267453067385570130168119360] checked0142
def B0141 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 1122433257470133441505582639969656021925279045255232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 422).pointIds 422)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M6667_6700.SplitData.node0141 := by
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

def B0140 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 393248, 374144419156711147385296005618919115861441583251520] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0141]
theorem treeEq0140 : B0140.tree = HexagonCover.NBand.M6667_6700.SplitData.node0140 := by
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
  · exact treeEq0141

def B0139 : Block := .branch 119 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711148683370374995130933666600027947072] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0140, (.leaf 5 (Common.fact 419).pointIds 419), Tip0138_0142]
theorem treeEq0139 : B0139.tree = HexagonCover.NBand.M6667_6700.SplitData.node0139 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0140
  · rfl
  · rfl

def B0287 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M6667_6700.SplitData.node0287 := by
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

def B0286 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0287]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M6667_6700.SplitData.node0286 := by
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
  · exact treeEq0287

def B0290 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M6667_6700.SplitData.node0290 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0289 : Block := .branch 171 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 21778071482940061661655974875633165926432, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 656).pointIds 656), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 541).pointIds 541), B0290]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M6667_6700.SplitData.node0289 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0290

def B0288 : Block := .branch 169 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0289, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M6667_6700.SplitData.node0288 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0289
  · rfl
  · rfl

def B0285 : Block := .branch 119 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0286, (.leaf 5 (Common.fact 419).pointIds 419), B0288]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M6667_6700.SplitData.node0285 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0286
  · rfl
  · exact treeEq0288

def B0292 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M6667_6700.SplitData.node0292 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0291 : Block := .branch 171 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356811923176489970264571492362373784095784976, 21778071482940061661655974875633165926432, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 656).pointIds 656), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), B0292, (.leaf 5 (Common.fact 541).pointIds 541), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M6667_6700.SplitData.node0291 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0292
  · rfl
  · rfl

def B0284 : Block := .branch 112 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 21778071482940061661655974875633165926432, 6360455125664089502943103374907104242591572367507520] ![B0285, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B0291]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M6667_6700.SplitData.node0284 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0285
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0291

def B0283 : Block := .branch 138 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356811923176489970264571492362373784095784976, 21778071482940061661655974875633165926432, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B0284, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M6667_6700.SplitData.node0283 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0284
  · rfl
  · rfl

def B0282 : Block := .branch 172 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711149980810300101208994080872671477824] ![(.leaf 0 (Common.fact 641).pointIds 641), (.leaf 1 (Common.fact 629).pointIds 629), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 642).pointIds 642), (.leaf 5 (Common.fact 631).pointIds 631), B0283]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M6667_6700.SplitData.node0282 := by
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
  · exact treeEq0283

def B0138 : Block := .branch 111 ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711148683370374995130933666600027947072] ![B0139, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B0282]
theorem treeEq0138 : B0138.tree = HexagonCover.NBand.M6667_6700.SplitData.node0138 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0139
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0282

theorem accepted0138 : B0138.accepted = true := by decide +kernel
theorem checked0138 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0138 (maskNeeds ![2535301201047907534856718909825, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 374144419156711148683370374995130933666600027947072]) := by
  rw [← treeEq0138]
  exact B0138.sound accepted0138
#print axioms checked0138

end HexagonCover.NBand.M6667_6700.SplitTree.Run0003
