import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0070
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0071
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip5061_5064 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5064 ![385, 302231599018845369533954, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0070.checked5064
def Tip5061_5085 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5085 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0070.checked5085
def B5084 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5084 : B5084.tree = HexagonCover.NBand.M7300_7500.SplitData.node5084 := by
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

def B5083 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5084, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5083 : B5083.tree = HexagonCover.NBand.M7300_7500.SplitData.node5083 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5084
  · rfl
  · rfl

def B5082 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5083, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5082 : B5082.tree = HexagonCover.NBand.M7300_7500.SplitData.node5082 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5083
  · rfl

def B5081 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5082, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5081 : B5081.tree = HexagonCover.NBand.M7300_7500.SplitData.node5081 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5082
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5080 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5081]
theorem treeEq5080 : B5080.tree = HexagonCover.NBand.M7300_7500.SplitData.node5080 := by
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
  · exact treeEq5081

def B5079 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5080, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5079 : B5079.tree = HexagonCover.NBand.M7300_7500.SplitData.node5079 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5080
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5078 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5079, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5078 : B5078.tree = HexagonCover.NBand.M7300_7500.SplitData.node5078 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5079
  · rfl

def B5077 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5078, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5077 : B5077.tree = HexagonCover.NBand.M7300_7500.SplitData.node5077 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5078
  · rfl
  · rfl

def B5063 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5061_5064, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5077]
theorem treeEq5063 : B5063.tree = HexagonCover.NBand.M7300_7500.SplitData.node5063 := by
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
  · exact treeEq5077

def B5062 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5063, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5061_5085]
theorem treeEq5062 : B5062.tree = HexagonCover.NBand.M7300_7500.SplitData.node5062 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5063
  · rfl
  · rfl
  · rfl
  · rfl

def B5106 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1031).pointIds 1031)]
theorem treeEq5106 : B5106.tree = HexagonCover.NBand.M7300_7500.SplitData.node5106 := by
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

def B5105 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5106, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5105 : B5105.tree = HexagonCover.NBand.M7300_7500.SplitData.node5105 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5106
  · rfl
  · rfl

def B5104 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5105, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5104 : B5104.tree = HexagonCover.NBand.M7300_7500.SplitData.node5104 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5105
  · rfl

def B5103 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![B5104, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq5103 : B5103.tree = HexagonCover.NBand.M7300_7500.SplitData.node5103 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5104
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5102 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 723).pointIds 723), B5103, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq5102 : B5102.tree = HexagonCover.NBand.M7300_7500.SplitData.node5102 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5103
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5101 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5102]
theorem treeEq5101 : B5101.tree = HexagonCover.NBand.M7300_7500.SplitData.node5101 := by
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
  · exact treeEq5102

def B5100 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![B5101, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq5100 : B5100.tree = HexagonCover.NBand.M7300_7500.SplitData.node5100 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5101
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5099 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5100, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5099 : B5099.tree = HexagonCover.NBand.M7300_7500.SplitData.node5099 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5100
  · rfl

def B5098 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5099, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq5098 : B5098.tree = HexagonCover.NBand.M7300_7500.SplitData.node5098 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5099
  · rfl
  · rfl

def B5061 : Block := .branch 68 ![10384596192949733827821542456689025, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), B5062, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B5098]
theorem treeEq5061 : B5061.tree = HexagonCover.NBand.M7300_7500.SplitData.node5061 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5062
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5098

theorem accepted5061 : B5061.accepted = true := by decide +kernel
theorem checked5061 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5061 (maskNeeds ![10384596192949733827821542456689025, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5061]
  exact B5061.sound accepted5061
#print axioms checked5061

def B5130 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5130 : B5130.tree = HexagonCover.NBand.M7300_7500.SplitData.node5130 := by
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

def B5129 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5130, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5129 : B5129.tree = HexagonCover.NBand.M7300_7500.SplitData.node5129 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5130
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5128 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5129, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5128 : B5128.tree = HexagonCover.NBand.M7300_7500.SplitData.node5128 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5129
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5127 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5128, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5127 : B5127.tree = HexagonCover.NBand.M7300_7500.SplitData.node5127 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5126 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5127, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5126 : B5126.tree = HexagonCover.NBand.M7300_7500.SplitData.node5126 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5127
  · rfl

def B5125 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5126, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5125 : B5125.tree = HexagonCover.NBand.M7300_7500.SplitData.node5125 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5126
  · rfl
  · rfl

def B5124 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5125]
theorem treeEq5124 : B5124.tree = HexagonCover.NBand.M7300_7500.SplitData.node5124 := by
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
  · exact treeEq5125

def B5123 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5124, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5123 : B5123.tree = HexagonCover.NBand.M7300_7500.SplitData.node5123 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5124
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5122 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5123]
theorem treeEq5122 : B5122.tree = HexagonCover.NBand.M7300_7500.SplitData.node5122 := by
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
  · exact treeEq5123

def B5121 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5122, (.leaf 0 [] 0)]
theorem treeEq5121 : B5121.tree = HexagonCover.NBand.M7300_7500.SplitData.node5121 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5122
  · rfl

def B5120 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5121, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5120 : B5120.tree = HexagonCover.NBand.M7300_7500.SplitData.node5120 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5121
  · rfl

def B5119 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5120, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5119 : B5119.tree = HexagonCover.NBand.M7300_7500.SplitData.node5119 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5120
  · rfl
  · rfl

def B5118 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5119]
theorem treeEq5118 : B5118.tree = HexagonCover.NBand.M7300_7500.SplitData.node5118 := by
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
  · exact treeEq5119

theorem accepted5118 : B5118.accepted = true := by decide +kernel
theorem checked5118 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5118 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5118]
  exact B5118.sound accepted5118
#print axioms checked5118

def B5151 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq5151 : B5151.tree = HexagonCover.NBand.M7300_7500.SplitData.node5151 := by
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

def B5150 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5151, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq5150 : B5150.tree = HexagonCover.NBand.M7300_7500.SplitData.node5150 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5151
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5149 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![(.leaf 0 (Common.fact 906).pointIds 906), B5150, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq5149 : B5149.tree = HexagonCover.NBand.M7300_7500.SplitData.node5149 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5150
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5148 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5149, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq5148 : B5148.tree = HexagonCover.NBand.M7300_7500.SplitData.node5148 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5147 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5148, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5147 : B5147.tree = HexagonCover.NBand.M7300_7500.SplitData.node5147 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5148
  · rfl

def B5146 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742542087917883600937189638208] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5147, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq5146 : B5146.tree = HexagonCover.NBand.M7300_7500.SplitData.node5146 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5147
  · rfl
  · rfl

def B5145 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5146]
theorem treeEq5145 : B5145.tree = HexagonCover.NBand.M7300_7500.SplitData.node5145 := by
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
  · exact treeEq5146

def B5144 : Block := .branch 78 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B5145, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq5144 : B5144.tree = HexagonCover.NBand.M7300_7500.SplitData.node5144 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5145
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5143 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![B5144, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq5143 : B5143.tree = HexagonCover.NBand.M7300_7500.SplitData.node5143 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5144
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5142 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5143]
theorem treeEq5142 : B5142.tree = HexagonCover.NBand.M7300_7500.SplitData.node5142 := by
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
  · exact treeEq5143

def B5141 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5142, (.leaf 0 [] 0)]
theorem treeEq5141 : B5141.tree = HexagonCover.NBand.M7300_7500.SplitData.node5141 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5142
  · rfl

def B5140 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5141, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5140 : B5140.tree = HexagonCover.NBand.M7300_7500.SplitData.node5140 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5141
  · rfl

def B5139 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5140, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq5139 : B5139.tree = HexagonCover.NBand.M7300_7500.SplitData.node5139 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5140
  · rfl
  · rfl

theorem accepted5139 : B5139.accepted = true := by decide +kernel
theorem checked5139 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5139 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496]) := by
  rw [← treeEq5139]
  exact B5139.sound accepted5139
#print axioms checked5139

def B5166 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5166 : B5166.tree = HexagonCover.NBand.M7300_7500.SplitData.node5166 := by
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

def B5165 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5166, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5165 : B5165.tree = HexagonCover.NBand.M7300_7500.SplitData.node5165 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5166
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5164 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5165, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5164 : B5164.tree = HexagonCover.NBand.M7300_7500.SplitData.node5164 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5165
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5163 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5164, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5163 : B5163.tree = HexagonCover.NBand.M7300_7500.SplitData.node5163 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5164
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5162 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5163, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5162 : B5162.tree = HexagonCover.NBand.M7300_7500.SplitData.node5162 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5163
  · rfl

def B5161 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5162, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5161 : B5161.tree = HexagonCover.NBand.M7300_7500.SplitData.node5161 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5162
  · rfl
  · rfl

def B5160 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5161]
theorem treeEq5160 : B5160.tree = HexagonCover.NBand.M7300_7500.SplitData.node5160 := by
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
  · exact treeEq5161

def B5159 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5160, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5159 : B5159.tree = HexagonCover.NBand.M7300_7500.SplitData.node5159 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5160
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5158 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5159]
theorem treeEq5158 : B5158.tree = HexagonCover.NBand.M7300_7500.SplitData.node5158 := by
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
  · exact treeEq5159

def B5157 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5158, (.leaf 0 [] 0)]
theorem treeEq5157 : B5157.tree = HexagonCover.NBand.M7300_7500.SplitData.node5157 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5158
  · rfl

def B5156 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5157, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5156 : B5156.tree = HexagonCover.NBand.M7300_7500.SplitData.node5156 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5157
  · rfl

def B5155 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5156, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5155 : B5155.tree = HexagonCover.NBand.M7300_7500.SplitData.node5155 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5156
  · rfl
  · rfl

def B5154 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5155]
theorem treeEq5154 : B5154.tree = HexagonCover.NBand.M7300_7500.SplitData.node5154 := by
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
  · exact treeEq5155

theorem accepted5154 : B5154.accepted = true := by decide +kernel
theorem checked5154 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5154 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5154]
  exact B5154.sound accepted5154
#print axioms checked5154

def B5187 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq5187 : B5187.tree = HexagonCover.NBand.M7300_7500.SplitData.node5187 := by
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

def B5186 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5187, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq5186 : B5186.tree = HexagonCover.NBand.M7300_7500.SplitData.node5186 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5187
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5185 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![(.leaf 0 (Common.fact 906).pointIds 906), B5186, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq5185 : B5185.tree = HexagonCover.NBand.M7300_7500.SplitData.node5185 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5186
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5184 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5185, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq5184 : B5184.tree = HexagonCover.NBand.M7300_7500.SplitData.node5184 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5185
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5183 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5184, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5183 : B5183.tree = HexagonCover.NBand.M7300_7500.SplitData.node5183 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5184
  · rfl

def B5182 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742542087917883600937189638208] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5183, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq5182 : B5182.tree = HexagonCover.NBand.M7300_7500.SplitData.node5182 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5183
  · rfl
  · rfl

def B5181 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5182]
theorem treeEq5181 : B5181.tree = HexagonCover.NBand.M7300_7500.SplitData.node5181 := by
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
  · exact treeEq5182

def B5180 : Block := .branch 78 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B5181, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq5180 : B5180.tree = HexagonCover.NBand.M7300_7500.SplitData.node5180 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5181
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5179 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![B5180, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq5179 : B5179.tree = HexagonCover.NBand.M7300_7500.SplitData.node5179 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5180
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5178 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5179]
theorem treeEq5178 : B5178.tree = HexagonCover.NBand.M7300_7500.SplitData.node5178 := by
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
  · exact treeEq5179

def B5177 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5178, (.leaf 0 [] 0)]
theorem treeEq5177 : B5177.tree = HexagonCover.NBand.M7300_7500.SplitData.node5177 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5178
  · rfl

def B5176 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5177, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5176 : B5176.tree = HexagonCover.NBand.M7300_7500.SplitData.node5176 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5177
  · rfl

def B5175 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5176, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq5175 : B5175.tree = HexagonCover.NBand.M7300_7500.SplitData.node5175 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5176
  · rfl
  · rfl

theorem accepted5175 : B5175.accepted = true := by decide +kernel
theorem checked5175 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5175 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496]) := by
  rw [← treeEq5175]
  exact B5175.sound accepted5175
#print axioms checked5175

end HexagonCover.NBand.M7300_7500.SplitTree.Run0071
