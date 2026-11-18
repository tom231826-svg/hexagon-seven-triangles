import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0198_0205 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0205 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 170141183460546602984142639983065325576, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785510068395610909051707694035228958278549568] HexagonCover.NBand.M6667_6700.SplitTree.Run0001.checked0205
def B0204 : Block := .branch 132 ![385, 1538, 6148, 24584, 748288838314102858854128511277663655278700998524944, 393248, 4863877449037585194148784371228263085367993751306304] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M6667_6700.SplitData.node0204 := by
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

def B0203 : Block := .branch 170 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 748289195300250607207619269142403816657550418477072, 187163553430688754962459388889728994204687861678112, 3367299772410740605908211102526789273240318827298880] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), (.leaf 5 (Common.fact 564).pointIds 564), B0204]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M6667_6700.SplitData.node0203 := by
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
  · exact treeEq0204

def B0202 : Block := .branch 167 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 748289195300250607207619269142403816657550418477072, 91343852333181432387730302044767688728496177184, 3367299772410740607531437696119037021856847281782848] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 560).pointIds 560), B0203, (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M6667_6700.SplitData.node0202 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203
  · rfl

def B0201 : Block := .branch 129 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 170141183460546602984142639983065325576, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877067174780767286014094742126656] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B0202, (.leaf 5 (Common.fact 559).pointIds 559), Tip0198_0205]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M6667_6700.SplitData.node0201 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0202
  · rfl
  · rfl

def B0227 : Block := .branch 172 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 332306999023600220681288032251305992, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 374144419162325806114972936607638070100909738164288] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 594).pointIds 594), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 591).pointIds 591), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M6667_6700.SplitData.node0227 := by
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

def B0226 : Block := .branch 132 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 332306999023600220681288032251305992, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 374144419156881288244237921192224076382001446780992] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 572).pointIds 572), (.leaf 5 (Common.fact 142).pointIds 142), B0227]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M6667_6700.SplitData.node0226 := by
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
  · exact treeEq0227

def B0225 : Block := .branch 167 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 332306999023600220681288032251305992, 748288838313422294120286634350736906063837462102032, 1496669026054364069305616784387448147978493796679712, 374144419156881289866830689484357710297781549662272] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), B0226, (.leaf 5 (Common.fact 571).pointIds 571), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M6667_6700.SplitData.node0225 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0226
  · rfl
  · rfl

def B0224 : Block := .branch 170 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 332306999023600220681288032251305992, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 385836432255868795579381106609551349062460778217536] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), B0225, (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M6667_6700.SplitData.node0224 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0225
  · rfl

def B0200 : Block := .branch 127 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 332306999023600220681288032251305992, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877067174780767286014094742126656] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0201, (.leaf 4 (Common.fact 554).pointIds 554), (.leaf 5 (Common.fact 481).pointIds 481), B0224]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M6667_6700.SplitData.node0200 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0201
  · rfl
  · rfl
  · exact treeEq0224

def B0231 : Block := .branch 172 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 162417810525494347403032279408648, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3367299772416185456086578889471285607611740540371008] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 597).pointIds 597), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 591).pointIds 591), (.leaf 6 (Common.fact 598).pointIds 598)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M6667_6700.SplitData.node0231 := by
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

def B0230 : Block := .branch 132 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 162417810525494347403032279408648, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3367299772410740938215843874055871613892832248987712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 572).pointIds 572), (.leaf 5 (Common.fact 142).pointIds 142), B0231]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M6667_6700.SplitData.node0230 := by
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
  · exact treeEq0231

def B0229 : Block := .branch 167 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 162417810525494347403032279408648, 748288838313422294120286634350736906063837462102032, 1496669026054364069305616784387448147978493796679712, 3367299772410740939838436642348005247808612351868992] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), B0230, (.leaf 5 (Common.fact 571).pointIds 571), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M6667_6700.SplitData.node0229 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl
  · rfl

def B0228 : Block := .branch 170 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 162417810525494347403032279408648, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509388163184066121009735511965859812212800] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), B0229, (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M6667_6700.SplitData.node0228 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0229
  · rfl

def B0199 : Block := .branch 118 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 162417810525494347403032279408648, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877067174780767286014094742126656] ![(.leaf 0 (Common.fact 472).pointIds 472), (.leaf 1 (Common.fact 473).pointIds 473), (.leaf 2 (Common.fact 474).pointIds 474), B0200, (.leaf 4 (Common.fact 553).pointIds 553), (.leaf 5 (Common.fact 476).pointIds 476), B0228]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M6667_6700.SplitData.node0199 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0200
  · rfl
  · rfl
  · exact treeEq0228

def B0235 : Block := .branch 172 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 158533696280984011454269120520, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3367299772416185123941839220071530745051553480572992] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 600).pointIds 600), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 591).pointIds 591), (.leaf 6 (Common.fact 601).pointIds 601)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M6667_6700.SplitData.node0235 := by
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

def B0234 : Block := .branch 132 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 158533696280984011454269120520, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3367299772410740606071104204656116751332645189189696] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 572).pointIds 572), (.leaf 5 (Common.fact 142).pointIds 142), B0235]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M6667_6700.SplitData.node0234 := by
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
  · exact treeEq0235

def B0233 : Block := .branch 167 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 158533696280984011454269120520, 748288838313422294120286634350736906063837462102032, 1496669026054364069305616784387448147978493796679712, 3367299772410740607693696972948250385248425292070976] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), B0234, (.leaf 5 (Common.fact 571).pointIds 571), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M6667_6700.SplitData.node0233 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0234
  · rfl
  · rfl

def B0232 : Block := .branch 170 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 158533696280984011454269120520, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387831039326451609980649405672752414784] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), B0233, (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M6667_6700.SplitData.node0232 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0233
  · rfl

def B0198 : Block := .branch 107 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 158533696280984011454269120520, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877067174780767286014094742126656] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), B0199, (.leaf 4 (Common.fact 552).pointIds 552), (.leaf 5 (Common.fact 471).pointIds 471), B0232]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M6667_6700.SplitData.node0198 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0199
  · rfl
  · rfl
  · exact treeEq0232

theorem accepted0198 : B0198.accepted = true := by decide +kernel
theorem checked0198 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0198 (maskNeeds ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 158533696280984011454269120520, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877067174780767286014094742126656]) := by
  rw [← treeEq0198]
  exact B0198.sound accepted0198
#print axioms checked0198

def Tip0186_0198 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0198 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 158533696280984011454269120520, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877067174780767286014094742126656] checked0198
def B0188 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 1134125270568781329140691457430896011202900625195072] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 535).pointIds 535)]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M6667_6700.SplitData.node0188 := by
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

def B0187 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1394136857275084884809445766647954362433552, 393248, 385836432255359035020404823080159105139063163191360] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0188]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M6667_6700.SplitData.node0187 := by
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
  · exact treeEq0188

def B0239 : Block := .branch 172 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3367299772416185123779738399567345910335162558185536] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 591).pointIds 591), (.leaf 6 (Common.fact 604).pointIds 604)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M6667_6700.SplitData.node0239 := by
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

def B0238 : Block := .branch 132 ![58488627962965565822734697405106618753, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 935361047891777867650358292938421132579796827602960, 1496669026054364069305616784387448147978493796679712, 3367299772410740605909003384151931916616254266802240] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 572).pointIds 572), (.leaf 5 (Common.fact 142).pointIds 142), B0239]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M6667_6700.SplitData.node0238 := by
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
  · exact treeEq0239

def B0237 : Block := .branch 167 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748288838313422294120286634350736906063837462102032, 1496669026054364069305616784387448147978493796679712, 3367299772410740607531596152444065550532034369683520] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), B0238, (.leaf 5 (Common.fact 571).pointIds 571), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M6667_6700.SplitData.node0237 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0238
  · rfl
  · rfl

def B0236 : Block := .branch 170 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877225631105795814689281830027328] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), B0237, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M6667_6700.SplitData.node0236 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0237
  · rfl

def B0197 : Block := .branch 97 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 91349427519481065043515685974335850818872672288, 3378991785509387830877067174780767286014094742126656] ![(.leaf 0 (Common.fact 462).pointIds 462), (.leaf 1 (Common.fact 463).pointIds 463), (.leaf 2 (Common.fact 464).pointIds 464), Tip0186_0198, (.leaf 4 (Common.fact 551).pointIds 551), (.leaf 5 (Common.fact 466).pointIds 466), B0236]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M6667_6700.SplitData.node0197 := by
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
  · exact treeEq0236

def B0196 : Block := .branch 142 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 91343852333181432387730302044767688728496177184, 3378991785509387830877067174780767286014094742126656] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 549).pointIds 549), B0197, (.leaf 6 (Common.fact 550).pointIds 550)]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M6667_6700.SplitData.node0196 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0197
  · rfl

def B0195 : Block := .branch 150 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 91343852333181432387730302044767688728496177184, 3378991785509387830877067329523272196686629104517184] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 547).pointIds 547), B0196, (.leaf 6 (Common.fact 548).pointIds 548)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M6667_6700.SplitData.node0195 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0196
  · rfl

def B0194 : Block := .branch 156 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 393248, 3378991785509387830877067329523272196686629104517184] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 546).pointIds 546), B0195, (.leaf 0 [] 0)]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M6667_6700.SplitData.node0194 := by
  change Tree.branch (156 : Fin 173) _ = Tree.branch (156 : Fin 173) _
  apply congrArg (Tree.branch (156 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0195
  · rfl

def B0193 : Block := .branch 164 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 393248, 3378991785509387830877067329523272196686629104517184] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 545).pointIds 545), B0194, (.leaf 0 [] 0)]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M6667_6700.SplitData.node0193 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194
  · rfl

def B0192 : Block := .branch 166 ![58488630498266766279193500398513029505, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 393248, 3378991785509387830877067329523272196686629104517184] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 544).pointIds 544), B0193, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M6667_6700.SplitData.node0192 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0193
  · rfl

def B0191 : Block := .branch 158 ![58488630498266766279193500398513029505, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 393248, 3378991785509387830877067329523272196686629104517184] ![(.leaf 0 (Common.fact 542).pointIds 542), B0192, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M6667_6700.SplitData.node0191 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0192
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0190 : Block := .branch 171 ![58488630498266766279193500398513029505, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 748289195299570042473777392215477067442686882054160, 21778071482940061661655974875633165926432, 385836432255698654395920792120324572431279256502336] ![(.leaf 0 (Common.fact 537).pointIds 537), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 541).pointIds 541), B0191]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M6667_6700.SplitData.node0190 := by
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
  · exact treeEq0191

def B0189 : Block := .branch 169 ![58488630498266766279193500398513029505, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 356986147748353490757864740161378849420050448, 21778071482940061661655974875633165926432, 385836432255698654395920792120324572431279256502336] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0190, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 536).pointIds 536)]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M6667_6700.SplitData.node0189 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0190
  · rfl
  · rfl

def B0186 : Block := .branch 128 ![58488630498266766279193500398513029505, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21778071482940061661655974875633165926432, 385836432255359036642997746114797649727377628463168] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0187, (.leaf 5 (Common.fact 439).pointIds 439), B0189]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M6667_6700.SplitData.node0186 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0187
  · rfl
  · exact treeEq0189

theorem accepted0186 : B0186.accepted = true := by decide +kernel
theorem checked0186 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0186 (maskNeeds ![58488630498266766279193500398513029505, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21778071482940061661655974875633165926432, 385836432255359036642997746114797649727377628463168]) := by
  rw [← treeEq0186]
  exact B0186.sound accepted0186
#print axioms checked0186

def Tip0185_0186 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0186 ![58488630498266766279193500398513029505, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21778071482940061661655974875633165926432, 385836432255359036642997746114797649727377628463168] checked0186
def B0253 : Block := .branch 172 ![15953332097848257889812871476135592321, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 77371252455336267181219848, 935361047891777867650358292938421132579796827602960, 1496669026054406604601481901695381069804422767706144, 3367299772419587947448789327876951127734293152399424] ![(.leaf 0 (Common.fact 617).pointIds 617), (.leaf 1 (Common.fact 587).pointIds 587), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 579).pointIds 579), (.leaf 5 (Common.fact 618).pointIds 618), (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M6667_6700.SplitData.node0253 := by
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

def B0252 : Block := .branch 128 ![15953332097848257889812871476135592321, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 935361049459799014422042732577651323625384745992208, 1496669026054406604601481901695381069804422767706144, 3367299772419247665081868389413487753126861384187968] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 616).pointIds 616), (.leaf 5 (Common.fact 439).pointIds 439), B0253]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M6667_6700.SplitData.node0252 := by
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
  · exact treeEq0253

def B0251 : Block := .branch 129 ![15953332097848257889812871476135592321, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 935361049459799014422042732577651323625384745992208, 1496669026054406604601481901695381069804422767706144, 3367299772418567100348026512486561003911997847765056] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 615).pointIds 615), (.leaf 5 (Common.fact 559).pointIds 559), B0252]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M6667_6700.SplitData.node0251 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0252

def B0250 : Block := .branch 130 ![15953332097848257889812871476135592321, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 935361049459799014422042732577651323625384745992208, 1496669026054406604601481901695381069804422767706144, 3367299772418567100348026512486561003911997847765056] ![(.leaf 0 (Common.fact 169).pointIds 169), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 614).pointIds 614), (.leaf 5 (Common.fact 173).pointIds 173), B0251]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M6667_6700.SplitData.node0250 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0251

def B0249 : Block := .branch 131 ![15953332097848257889812871476135592321, 365375409332725729550921208179070756013494765058, 77919046967349146032132, 96714065569170333976518664, 935361049459799014422042732577651323625384745992208, 1496669026054406604601481901695381069804422767706144, 3367299772415844841412659004778854007052543702073408] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 613).pointIds 613), (.leaf 5 (Common.fact 148).pointIds 148), B0250]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M6667_6700.SplitData.node0249 := by
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
  · exact treeEq0250

def B0248 : Block := .branch 170 ![15953332097848257889812871476135592321, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 96714065569170333976518664, 935361406271722190912012997149143685999168841678864, 91349427562016360908632993907257676747843698720, 3367299772415844841412659004778854007052543702073408] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 562).pointIds 562), (.leaf 2 (Common.fact 497).pointIds 497), (.leaf 3 (Common.fact 519).pointIds 519), (.leaf 4 (Common.fact 563).pointIds 563), B0249, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M6667_6700.SplitData.node0248 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0249
  · rfl

def B0247 : Block := .branch 132 ![15953332097848257889812871476135592321, 365375409332725729551540178198713446150944327170, 77919046967349146032132, 96714065569170333976518664, 935361406271722190912012997149143685999168841678864, 91349427562016360908632993907257676747843698720, 3367299772410400323541923989363440013333635410690112] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 611).pointIds 611), (.leaf 5 (Common.fact 142).pointIds 142), B0248]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M6667_6700.SplitData.node0247 := by
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
  · exact treeEq0248

def B0246 : Block := .branch 158 ![15953332097848257889812871476135592321, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 935361406271722190912012997149143685999168841678864, 91349427562016360908632993907257676747843698720, 3378991785509047546887553468025170277490882871033920] ![(.leaf 0 (Common.fact 542).pointIds 542), B0247, (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 610).pointIds 610)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M6667_6700.SplitData.node0246 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0247
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0245 : Block := .branch 142 ![15953332097848257889812871476135592321, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 935361406271722190912012997149143685999168841678864, 91343852375716728252847609977689514657467203616, 3378991785509047548510146236317303911406662973915200] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 609).pointIds 609), B0246, (.leaf 6 (Common.fact 550).pointIds 550)]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M6667_6700.SplitData.node0245 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0246
  · rfl

def B0244 : Block := .branch 150 ![15953332097848257889812871476135592321, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 935361406271722190912012997149143685999168841678864, 91343852375716728252847609977689514657467203616, 3378991785509047548510146391059808822079197336305728] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 608).pointIds 608), B0245, (.leaf 6 (Common.fact 548).pointIds 548)]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M6667_6700.SplitData.node0244 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0245
  · rfl

def B0243 : Block := .branch 156 ![15953332097848257889812871476135592321, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 935361406271722190912012997149143685999168841678864, 42535295865117307932921825928971419680, 3378991785509047548510146391059808822079197336305728] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 607).pointIds 607), B0244, (.leaf 0 [] 0)]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M6667_6700.SplitData.node0243 := by
  change Tree.branch (156 : Fin 173) _ = Tree.branch (156 : Fin 173) _
  apply congrArg (Tree.branch (156 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0244
  · rfl

def B0242 : Block := .branch 169 ![15953334633149458346271674469542003073, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 187072567958299896791726362798406779935331379675152, 42535295865117307932921825928971419680, 3378991785509047548510146391059808822079197336305728] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0243, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M6667_6700.SplitData.node0242 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0243
  · rfl
  · rfl

def B0241 : Block := .branch 171 ![15953334633149458346271674469542003073, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 187072567958299896791726362798406779935331379675152, 21820606778805178969588896701562136952864, 385836432255358372028999853656861197823847488290880] ![(.leaf 0 (Common.fact 537).pointIds 537), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 605).pointIds 605), (.leaf 5 (Common.fact 541).pointIds 541), B0242]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M6667_6700.SplitData.node0241 := by
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
  · exact treeEq0242

def B0240 : Block := .branch 167 ![15953334633149458346271674469542003073, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21820606778805178969588896701562136952864, 385836432255358372028999853656861197823847488290880] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), B0241, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M6667_6700.SplitData.node0240 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0241
  · rfl
  · rfl

def B0185 : Block := .branch 125 ![15953334633149458346271674469542003073, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21778071482940061661655974875633165926432, 385836432255359036642997746114797649727377628463168] ![Tip0185_0186, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0240, (.leaf 6 (Common.fact 456).pointIds 456)]
theorem treeEq0185 : B0185.tree = HexagonCover.NBand.M6667_6700.SplitData.node0185 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0240
  · rfl

theorem accepted0185 : B0185.accepted = true := by decide +kernel
theorem checked0185 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0185 (maskNeeds ![15953334633149458346271674469542003073, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 358379944323261654704210722553419372014174224, 21778071482940061661655974875633165926432, 385836432255359036642997746114797649727377628463168]) := by
  rw [← treeEq0185]
  exact B0185.sound accepted0185
#print axioms checked0185

def B0271 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M6667_6700.SplitData.node0271 := by
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

def B0270 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0271]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M6667_6700.SplitData.node0270 := by
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
  · exact treeEq0271

def B0273 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M6667_6700.SplitData.node0273 := by
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

def B0272 : Block := .branch 171 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 537).pointIds 537), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), B0273, (.leaf 5 (Common.fact 541).pointIds 541), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M6667_6700.SplitData.node0272 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0273
  · rfl
  · rfl

def B0269 : Block := .branch 128 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0270, (.leaf 5 (Common.fact 439).pointIds 439), B0272]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M6667_6700.SplitData.node0269 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0270
  · rfl
  · exact treeEq0272

def B0275 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M6667_6700.SplitData.node0275 := by
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

def B0274 : Block := .branch 169 ![2535301200457611724498013258113, 618970019642691236961191426, 77919046967349146032132, 77371252455336267181219848, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0275]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M6667_6700.SplitData.node0274 := by
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
  · exact treeEq0275

def B0268 : Block := .branch 127 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 1393796574908163946345982392040522594222096, 21778071482940061661655974875633165926432, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0269, B0274, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M6667_6700.SplitData.node0268 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0269
  · exact treeEq0274
  · rfl
  · rfl

def B0278 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211146376720301756098226914417561547283988496, 393248, 9353610478917783993416199894347817055727507503317056] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 616).pointIds 616), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M6667_6700.SplitData.node0278 := by
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

def B0277 : Block := .branch 171 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 187072211146376720301756098226914417561547283988496, 21778071482940061661655974875633165926432, 6360455125664094816935053356944869431472157655302208] ![(.leaf 0 (Common.fact 537).pointIds 537), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 605).pointIds 605), (.leaf 5 (Common.fact 541).pointIds 541), B0278]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M6667_6700.SplitData.node0277 := by
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
  · exact treeEq0278

def B0276 : Block := .branch 167 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 1568021146771684439639230191045587918487568, 21820606778805178969588896701562136952864, 6360455125664094818557646434722012886733006482964544] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 307).pointIds 307), B0277, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M6667_6700.SplitData.node0276 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0277
  · rfl
  · rfl

def B0267 : Block := .branch 125 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 1568021146771684439639230191045587918487568, 21778071482940061661655974875633165926432, 6360455125664098141627635897011695146250657183825984] ![B0268, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0276, (.leaf 6 (Common.fact 456).pointIds 456)]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M6667_6700.SplitData.node0267 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0268
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0276
  · rfl

def B0281 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M6667_6700.SplitData.node0281 := by
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

def B0280 : Block := .branch 171 ![2596148429267414967186752771457409, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 748288838313422294120286634350736906063837462102032, 21778071482940061661655974875633165926432, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 537).pointIds 537), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 539).pointIds 539), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 541).pointIds 541), B0281]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M6667_6700.SplitData.node0280 := by
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
  · exact treeEq0281

def B0279 : Block := .branch 169 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 98320, 21778071482940061661655974875633165926432, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 387).pointIds 387), (.leaf 1 (Common.fact 363).pointIds 363), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 353).pointIds 353), B0280, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M6667_6700.SplitData.node0279 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0280
  · rfl
  · rfl

def B0266 : Block := .branch 123 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 1568021146771684439639230191045587918487568, 21778071482940061661655974875633165926432, 6360455125664098141627635897011695146250657183825984] ![B0267, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0279]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M6667_6700.SplitData.node0266 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0267
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0279

def B0265 : Block := .branch 172 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 1568021146771684439639230191045587918487568, 21778071482940061661655974875633165926432, 374144419156719788665342822205799897739957487796288] ![(.leaf 0 (Common.fact 628).pointIds 628), (.leaf 1 (Common.fact 629).pointIds 629), (.leaf 2 (Common.fact 582).pointIds 582), (.leaf 3 (Common.fact 603).pointIds 603), (.leaf 4 (Common.fact 630).pointIds 630), (.leaf 5 (Common.fact 631).pointIds 631), B0266]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M6667_6700.SplitData.node0265 := by
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
  · exact treeEq0266

def B0264 : Block := .branch 140 ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 174224571863520493293247799005065324363792, 21778071482940061661655974875633165926432, 374144419156719788665342822205799897739957487796288] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0265, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 627).pointIds 627)]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M6667_6700.SplitData.node0264 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0265
  · rfl
  · rfl

theorem accepted0264 : B0264.accepted = true := by decide +kernel
theorem checked0264 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0264 (maskNeeds ![2598683730467871425989746177868161, 618970019642691236961191426, 77919046967349146032132, 96714065569170333976518664, 174224571863520493293247799005065324363792, 21778071482940061661655974875633165926432, 374144419156719788665342822205799897739957487796288]) := by
  rw [← treeEq0264]
  exact B0264.sound accepted0264
#print axioms checked0264

end HexagonCover.NBand.M6667_6700.SplitTree.Run0002
