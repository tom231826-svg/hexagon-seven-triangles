import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0075
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0076
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B5516 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq5516 : B5516.tree = HexagonCover.NBand.M7300_7500.SplitData.node5516 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5515 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5516, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq5515 : B5515.tree = HexagonCover.NBand.M7300_7500.SplitData.node5515 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5516
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5514 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![(.leaf 0 (Common.fact 906).pointIds 906), B5515, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq5514 : B5514.tree = HexagonCover.NBand.M7300_7500.SplitData.node5514 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5515
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5513 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5514, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq5513 : B5513.tree = HexagonCover.NBand.M7300_7500.SplitData.node5513 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5514
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5512 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5513, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5512 : B5512.tree = HexagonCover.NBand.M7300_7500.SplitData.node5512 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5513
  · rfl

def B5511 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742542087917883600937189638208] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5512, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq5511 : B5511.tree = HexagonCover.NBand.M7300_7500.SplitData.node5511 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5512
  · rfl
  · rfl

def B5510 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5511]
theorem treeEq5510 : B5510.tree = HexagonCover.NBand.M7300_7500.SplitData.node5510 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5511

def B5509 : Block := .branch 78 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B5510, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq5509 : B5509.tree = HexagonCover.NBand.M7300_7500.SplitData.node5509 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5510
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5508 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![B5509, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq5508 : B5508.tree = HexagonCover.NBand.M7300_7500.SplitData.node5508 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5509
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5507 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5508]
theorem treeEq5507 : B5507.tree = HexagonCover.NBand.M7300_7500.SplitData.node5507 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5508

def B5506 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5507, (.leaf 0 [] 0)]
theorem treeEq5506 : B5506.tree = HexagonCover.NBand.M7300_7500.SplitData.node5506 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5507
  · rfl

def B5505 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5506, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5505 : B5505.tree = HexagonCover.NBand.M7300_7500.SplitData.node5505 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5506
  · rfl

def B5504 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5505, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq5504 : B5504.tree = HexagonCover.NBand.M7300_7500.SplitData.node5504 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5505
  · rfl
  · rfl

theorem accepted5504 : B5504.accepted = true := by decide +kernel
theorem checked5504 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5504 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496]) := by
  rw [← treeEq5504]
  exact B5504.sound accepted5504
#print axioms checked5504

def Tip5445_5447 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5447 ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0075.checked5447
def Tip5445_5468 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5468 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0075.checked5468
def B5467 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5467 : B5467.tree = HexagonCover.NBand.M7300_7500.SplitData.node5467 := by
  change Tree.branch (121 : Fin 172) _ = Tree.branch (121 : Fin 172) _
  apply congrArg (Tree.branch (121 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5466 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5467, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5466 : B5466.tree = HexagonCover.NBand.M7300_7500.SplitData.node5466 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5467
  · rfl
  · rfl

def B5465 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5466, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5465 : B5465.tree = HexagonCover.NBand.M7300_7500.SplitData.node5465 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5466
  · rfl

def B5464 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5465, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5464 : B5464.tree = HexagonCover.NBand.M7300_7500.SplitData.node5464 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5465
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5463 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5464]
theorem treeEq5463 : B5463.tree = HexagonCover.NBand.M7300_7500.SplitData.node5463 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5464

def B5462 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5463, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5462 : B5462.tree = HexagonCover.NBand.M7300_7500.SplitData.node5462 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5463
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5461 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5462, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5461 : B5461.tree = HexagonCover.NBand.M7300_7500.SplitData.node5461 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5462
  · rfl

def B5460 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5461, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5460 : B5460.tree = HexagonCover.NBand.M7300_7500.SplitData.node5460 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5461
  · rfl
  · rfl

def B5446 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5445_5447, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5460]
theorem treeEq5446 : B5446.tree = HexagonCover.NBand.M7300_7500.SplitData.node5446 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5460

def B5445 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5446, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5445_5468]
theorem treeEq5445 : B5445.tree = HexagonCover.NBand.M7300_7500.SplitData.node5445 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5446
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5445 : B5445.accepted = true := by decide +kernel
theorem checked5445 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5445 (maskNeeds ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5445]
  exact B5445.sound accepted5445
#print axioms checked5445

def Tip5371_5410 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5410 ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0075.checked5410
def Tip5371_5431 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5431 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0075.checked5431
def Tip5371_5372 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5372 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0075.checked5372
def B5430 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5430 : B5430.tree = HexagonCover.NBand.M7300_7500.SplitData.node5430 := by
  change Tree.branch (121 : Fin 172) _ = Tree.branch (121 : Fin 172) _
  apply congrArg (Tree.branch (121 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5429 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5430, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5429 : B5429.tree = HexagonCover.NBand.M7300_7500.SplitData.node5429 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5430
  · rfl
  · rfl

def B5428 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5429, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5428 : B5428.tree = HexagonCover.NBand.M7300_7500.SplitData.node5428 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5429
  · rfl

def B5427 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5428, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5427 : B5427.tree = HexagonCover.NBand.M7300_7500.SplitData.node5427 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5428
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5426 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5427]
theorem treeEq5426 : B5426.tree = HexagonCover.NBand.M7300_7500.SplitData.node5426 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5427

def B5425 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5426, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5425 : B5425.tree = HexagonCover.NBand.M7300_7500.SplitData.node5425 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5426
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5424 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5425, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5424 : B5424.tree = HexagonCover.NBand.M7300_7500.SplitData.node5424 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5425
  · rfl

def B5423 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5424, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5423 : B5423.tree = HexagonCover.NBand.M7300_7500.SplitData.node5423 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5424
  · rfl
  · rfl

def B5409 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5371_5410, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5423]
theorem treeEq5409 : B5409.tree = HexagonCover.NBand.M7300_7500.SplitData.node5409 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5423

def B5408 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5409, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5371_5431]
theorem treeEq5408 : B5408.tree = HexagonCover.NBand.M7300_7500.SplitData.node5408 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5409
  · rfl
  · rfl
  · rfl
  · rfl

def B5371 : Block := .branch 74 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip5371_5372, B5408, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq5371 : B5371.tree = HexagonCover.NBand.M7300_7500.SplitData.node5371 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5408
  · rfl
  · rfl
  · rfl

theorem accepted5371 : B5371.accepted = true := by decide +kernel
theorem checked5371 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5371 (maskNeeds ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5371]
  exact B5371.sound accepted5371
#print axioms checked5371

def B5533 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5533 : B5533.tree = HexagonCover.NBand.M7300_7500.SplitData.node5533 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5532 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5533, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5532 : B5532.tree = HexagonCover.NBand.M7300_7500.SplitData.node5532 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5533
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5531 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5532, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5531 : B5531.tree = HexagonCover.NBand.M7300_7500.SplitData.node5531 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5530 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5531, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5530 : B5530.tree = HexagonCover.NBand.M7300_7500.SplitData.node5530 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5531
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5529 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5530, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5529 : B5529.tree = HexagonCover.NBand.M7300_7500.SplitData.node5529 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5530
  · rfl

def B5528 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5529, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5528 : B5528.tree = HexagonCover.NBand.M7300_7500.SplitData.node5528 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5529
  · rfl
  · rfl

def B5527 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5528]
theorem treeEq5527 : B5527.tree = HexagonCover.NBand.M7300_7500.SplitData.node5527 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5528

def B5526 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5527, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5526 : B5526.tree = HexagonCover.NBand.M7300_7500.SplitData.node5526 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5527
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5525 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5526]
theorem treeEq5525 : B5525.tree = HexagonCover.NBand.M7300_7500.SplitData.node5525 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5526

def B5524 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5525, (.leaf 0 [] 0)]
theorem treeEq5524 : B5524.tree = HexagonCover.NBand.M7300_7500.SplitData.node5524 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5525
  · rfl

def B5523 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5524, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5523 : B5523.tree = HexagonCover.NBand.M7300_7500.SplitData.node5523 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5524
  · rfl

def B5522 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5523, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5522 : B5522.tree = HexagonCover.NBand.M7300_7500.SplitData.node5522 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5523
  · rfl
  · rfl

def B5521 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5522]
theorem treeEq5521 : B5521.tree = HexagonCover.NBand.M7300_7500.SplitData.node5521 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5522

theorem accepted5521 : B5521.accepted = true := by decide +kernel
theorem checked5521 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5521 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5521]
  exact B5521.sound accepted5521
#print axioms checked5521

def B5554 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq5554 : B5554.tree = HexagonCover.NBand.M7300_7500.SplitData.node5554 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5553 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5554, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq5553 : B5553.tree = HexagonCover.NBand.M7300_7500.SplitData.node5553 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5554
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5552 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![(.leaf 0 (Common.fact 906).pointIds 906), B5553, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq5552 : B5552.tree = HexagonCover.NBand.M7300_7500.SplitData.node5552 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5553
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5551 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5552, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq5551 : B5551.tree = HexagonCover.NBand.M7300_7500.SplitData.node5551 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5552
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5550 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5551, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5550 : B5550.tree = HexagonCover.NBand.M7300_7500.SplitData.node5550 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5551
  · rfl

def B5549 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742542087917883600937189638208] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5550, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq5549 : B5549.tree = HexagonCover.NBand.M7300_7500.SplitData.node5549 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5550
  · rfl
  · rfl

def B5548 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5549]
theorem treeEq5548 : B5548.tree = HexagonCover.NBand.M7300_7500.SplitData.node5548 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5549

def B5547 : Block := .branch 78 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B5548, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq5547 : B5547.tree = HexagonCover.NBand.M7300_7500.SplitData.node5547 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5548
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5546 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![B5547, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq5546 : B5546.tree = HexagonCover.NBand.M7300_7500.SplitData.node5546 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5547
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5545 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5546]
theorem treeEq5545 : B5545.tree = HexagonCover.NBand.M7300_7500.SplitData.node5545 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5546

def B5544 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5545, (.leaf 0 [] 0)]
theorem treeEq5544 : B5544.tree = HexagonCover.NBand.M7300_7500.SplitData.node5544 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5545
  · rfl

def B5543 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5544, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5543 : B5543.tree = HexagonCover.NBand.M7300_7500.SplitData.node5543 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5544
  · rfl

def B5542 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5543, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq5542 : B5542.tree = HexagonCover.NBand.M7300_7500.SplitData.node5542 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5543
  · rfl
  · rfl

theorem accepted5542 : B5542.accepted = true := by decide +kernel
theorem checked5542 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5542 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496]) := by
  rw [← treeEq5542]
  exact B5542.sound accepted5542
#print axioms checked5542

def B5569 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5569 : B5569.tree = HexagonCover.NBand.M7300_7500.SplitData.node5569 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5568 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5569, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5568 : B5568.tree = HexagonCover.NBand.M7300_7500.SplitData.node5568 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5569
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5567 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5568, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5567 : B5567.tree = HexagonCover.NBand.M7300_7500.SplitData.node5567 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5568
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5566 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5567, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5566 : B5566.tree = HexagonCover.NBand.M7300_7500.SplitData.node5566 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5567
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5565 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5566, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5565 : B5565.tree = HexagonCover.NBand.M7300_7500.SplitData.node5565 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5566
  · rfl

def B5564 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5565, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5564 : B5564.tree = HexagonCover.NBand.M7300_7500.SplitData.node5564 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5565
  · rfl
  · rfl

def B5563 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5564]
theorem treeEq5563 : B5563.tree = HexagonCover.NBand.M7300_7500.SplitData.node5563 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5564

def B5562 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5563, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5562 : B5562.tree = HexagonCover.NBand.M7300_7500.SplitData.node5562 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5563
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5561 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5562]
theorem treeEq5561 : B5561.tree = HexagonCover.NBand.M7300_7500.SplitData.node5561 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5562

def B5560 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5561, (.leaf 0 [] 0)]
theorem treeEq5560 : B5560.tree = HexagonCover.NBand.M7300_7500.SplitData.node5560 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5561
  · rfl

def B5559 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5560, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5559 : B5559.tree = HexagonCover.NBand.M7300_7500.SplitData.node5559 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5560
  · rfl

def B5558 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5559, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5558 : B5558.tree = HexagonCover.NBand.M7300_7500.SplitData.node5558 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5559
  · rfl
  · rfl

def B5557 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5558]
theorem treeEq5557 : B5557.tree = HexagonCover.NBand.M7300_7500.SplitData.node5557 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5558

theorem accepted5557 : B5557.accepted = true := by decide +kernel
theorem checked5557 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5557 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5557]
  exact B5557.sound accepted5557
#print axioms checked5557

end HexagonCover.NBand.M7300_7500.SplitTree.Run0076
