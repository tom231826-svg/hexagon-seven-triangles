import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0070
import HexagonCover.NBand.M7300_7500.SplitTree.Run0071
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0072
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip5116_5118 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5118 ![385, 302231599018845369533954, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0071.checked5118
def Tip5116_5139 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5139 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0071.checked5139
def B5138 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5138 : B5138.tree = HexagonCover.NBand.M7300_7500.SplitData.node5138 := by
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

def B5137 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5138, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5137 : B5137.tree = HexagonCover.NBand.M7300_7500.SplitData.node5137 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5138
  · rfl
  · rfl

def B5136 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5137, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5136 : B5136.tree = HexagonCover.NBand.M7300_7500.SplitData.node5136 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5137
  · rfl

def B5135 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5136, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5135 : B5135.tree = HexagonCover.NBand.M7300_7500.SplitData.node5135 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5136
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5134 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5135]
theorem treeEq5134 : B5134.tree = HexagonCover.NBand.M7300_7500.SplitData.node5134 := by
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
  · exact treeEq5135

def B5133 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5134, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5133 : B5133.tree = HexagonCover.NBand.M7300_7500.SplitData.node5133 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5134
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5132 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5133, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5132 : B5132.tree = HexagonCover.NBand.M7300_7500.SplitData.node5132 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5133
  · rfl

def B5131 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5132, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5131 : B5131.tree = HexagonCover.NBand.M7300_7500.SplitData.node5131 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5132
  · rfl
  · rfl

def B5117 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5116_5118, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5131]
theorem treeEq5117 : B5117.tree = HexagonCover.NBand.M7300_7500.SplitData.node5117 := by
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
  · exact treeEq5131

def B5116 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5117, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5116_5139]
theorem treeEq5116 : B5116.tree = HexagonCover.NBand.M7300_7500.SplitData.node5116 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5117
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5116 : B5116.accepted = true := by decide +kernel
theorem checked5116 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5116 (maskNeeds ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5116]
  exact B5116.sound accepted5116
#print axioms checked5116

def Tip5115_5154 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5154 ![385, 302231599018845369533954, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0071.checked5154
def Tip5115_5175 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5175 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0071.checked5175
def Tip5115_5116 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5116 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked5116
def B5174 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5174 : B5174.tree = HexagonCover.NBand.M7300_7500.SplitData.node5174 := by
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

def B5173 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5174, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5173 : B5173.tree = HexagonCover.NBand.M7300_7500.SplitData.node5173 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5174
  · rfl
  · rfl

def B5172 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5173, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5172 : B5172.tree = HexagonCover.NBand.M7300_7500.SplitData.node5172 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5173
  · rfl

def B5171 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5172, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5171 : B5171.tree = HexagonCover.NBand.M7300_7500.SplitData.node5171 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5172
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5170 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5171]
theorem treeEq5170 : B5170.tree = HexagonCover.NBand.M7300_7500.SplitData.node5170 := by
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
  · exact treeEq5171

def B5169 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5170, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5169 : B5169.tree = HexagonCover.NBand.M7300_7500.SplitData.node5169 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5170
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5168 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5169, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5168 : B5168.tree = HexagonCover.NBand.M7300_7500.SplitData.node5168 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5169
  · rfl

def B5167 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5168, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5167 : B5167.tree = HexagonCover.NBand.M7300_7500.SplitData.node5167 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5168
  · rfl
  · rfl

def B5153 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5115_5154, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5167]
theorem treeEq5153 : B5153.tree = HexagonCover.NBand.M7300_7500.SplitData.node5153 := by
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
  · exact treeEq5167

def B5152 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5153, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5115_5175]
theorem treeEq5152 : B5152.tree = HexagonCover.NBand.M7300_7500.SplitData.node5152 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5153
  · rfl
  · rfl
  · rfl
  · rfl

def B5115 : Block := .branch 74 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip5115_5116, B5152, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq5115 : B5115.tree = HexagonCover.NBand.M7300_7500.SplitData.node5115 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5152
  · rfl
  · rfl
  · rfl

theorem accepted5115 : B5115.accepted = true := by decide +kernel
theorem checked5115 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5115 (maskNeeds ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5115]
  exact B5115.sound accepted5115
#print axioms checked5115

def Tip4924_4927 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4927 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0070.checked4927
def Tip4924_5020 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5020 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] HexagonCover.NBand.M7300_7500.SplitTree.Run0070.checked5020
def Tip4924_5061 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5061 ![10384596192949733827821542456689025, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0071.checked5061
def B5019 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 890).pointIds 890), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq5019 : B5019.tree = HexagonCover.NBand.M7300_7500.SplitData.node5019 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5018 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5019, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5018 : B5018.tree = HexagonCover.NBand.M7300_7500.SplitData.node5018 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5019
  · rfl
  · rfl

def B5017 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B5018, (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq5017 : B5017.tree = HexagonCover.NBand.M7300_7500.SplitData.node5017 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5018
  · rfl

def B5016 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![B5017, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq5016 : B5016.tree = HexagonCover.NBand.M7300_7500.SplitData.node5016 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5017
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5015 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5016]
theorem treeEq5015 : B5015.tree = HexagonCover.NBand.M7300_7500.SplitData.node5015 := by
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
  · exact treeEq5016

def B5014 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![B5015, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq5014 : B5014.tree = HexagonCover.NBand.M7300_7500.SplitData.node5014 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5015
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5013 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954656563512503497104293952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B5014, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5013 : B5013.tree = HexagonCover.NBand.M7300_7500.SplitData.node5013 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5014
  · rfl

def B5012 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954656563512503497104293952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5013, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq5012 : B5012.tree = HexagonCover.NBand.M7300_7500.SplitData.node5012 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5013
  · rfl
  · rfl

def B4926 : Block := .branch 78 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip4924_4927, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5012]
theorem treeEq4926 : B4926.tree = HexagonCover.NBand.M7300_7500.SplitData.node4926 := by
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
  · exact treeEq5012

def B4925 : Block := .branch 76 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B4926, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip4924_5020]
theorem treeEq4925 : B4925.tree = HexagonCover.NBand.M7300_7500.SplitData.node4925 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4926
  · rfl
  · rfl
  · rfl
  · rfl

def B5060 : Block := .branch 91 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![Tip4924_5061, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq5060 : B5060.tree = HexagonCover.NBand.M7300_7500.SplitData.node5060 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5059 : Block := .branch 113 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B5060, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq5059 : B5059.tree = HexagonCover.NBand.M7300_7500.SplitData.node5059 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5060
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5058 : Block := .branch 135 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B5059, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq5058 : B5058.tree = HexagonCover.NBand.M7300_7500.SplitData.node5058 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5059
  · rfl

def B5057 : Block := .branch 138 ![385, 144115188075857410, 18446745173221185540, 79266867029957937205715427336, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B5058, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq5057 : B5057.tree = HexagonCover.NBand.M7300_7500.SplitData.node5057 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5058
  · rfl
  · rfl

def B5056 : Block := .branch 144 ![385, 144115188075857410, 18446745173221185540, 79266867029957937205715427336, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B5057, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq5056 : B5056.tree = HexagonCover.NBand.M7300_7500.SplitData.node5056 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5057
  · rfl

def B5055 : Block := .branch 149 ![385, 144115188075857410, 18446745173221185540, 79266867029957937205715427336, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B5056, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq5055 : B5055.tree = HexagonCover.NBand.M7300_7500.SplitData.node5055 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5056
  · rfl
  · rfl

def B5054 : Block := .branch 161 ![385, 144115188075857410, 18446745173221185540, 79266867029957937205715427336, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 830).pointIds 830), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B5055]
theorem treeEq5054 : B5054.tree = HexagonCover.NBand.M7300_7500.SplitData.node5054 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5055

def B4924 : Block := .branch 74 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), B4925, B5054, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq4924 : B4924.tree = HexagonCover.NBand.M7300_7500.SplitData.node4924 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4925
  · exact treeEq5054
  · rfl
  · rfl
  · rfl

theorem accepted4924 : B4924.accepted = true := by decide +kernel
theorem checked4924 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4924 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4924]
  exact B4924.sound accepted4924
#print axioms checked4924

def B5221 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5221 : B5221.tree = HexagonCover.NBand.M7300_7500.SplitData.node5221 := by
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

def B5220 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5221, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5220 : B5220.tree = HexagonCover.NBand.M7300_7500.SplitData.node5220 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5221
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5219 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5220, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5219 : B5219.tree = HexagonCover.NBand.M7300_7500.SplitData.node5219 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5220
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5218 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5219, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5218 : B5218.tree = HexagonCover.NBand.M7300_7500.SplitData.node5218 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5219
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5217 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5218, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5217 : B5217.tree = HexagonCover.NBand.M7300_7500.SplitData.node5217 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5218
  · rfl

def B5216 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5217, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5216 : B5216.tree = HexagonCover.NBand.M7300_7500.SplitData.node5216 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5217
  · rfl
  · rfl

def B5215 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5216]
theorem treeEq5215 : B5215.tree = HexagonCover.NBand.M7300_7500.SplitData.node5215 := by
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
  · exact treeEq5216

def B5214 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5215, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5214 : B5214.tree = HexagonCover.NBand.M7300_7500.SplitData.node5214 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5215
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5213 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5214]
theorem treeEq5213 : B5213.tree = HexagonCover.NBand.M7300_7500.SplitData.node5213 := by
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
  · exact treeEq5214

def B5212 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5213, (.leaf 0 [] 0)]
theorem treeEq5212 : B5212.tree = HexagonCover.NBand.M7300_7500.SplitData.node5212 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5213
  · rfl

def B5211 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5212, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5211 : B5211.tree = HexagonCover.NBand.M7300_7500.SplitData.node5211 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5212
  · rfl

def B5210 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5211, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5210 : B5210.tree = HexagonCover.NBand.M7300_7500.SplitData.node5210 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5211
  · rfl
  · rfl

def B5209 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5210]
theorem treeEq5209 : B5209.tree = HexagonCover.NBand.M7300_7500.SplitData.node5209 := by
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
  · exact treeEq5210

theorem accepted5209 : B5209.accepted = true := by decide +kernel
theorem checked5209 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5209 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5209]
  exact B5209.sound accepted5209
#print axioms checked5209

def B5242 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq5242 : B5242.tree = HexagonCover.NBand.M7300_7500.SplitData.node5242 := by
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

def B5241 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5242, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq5241 : B5241.tree = HexagonCover.NBand.M7300_7500.SplitData.node5241 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5242
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5240 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![(.leaf 0 (Common.fact 906).pointIds 906), B5241, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq5240 : B5240.tree = HexagonCover.NBand.M7300_7500.SplitData.node5240 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5241
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5239 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5240, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq5239 : B5239.tree = HexagonCover.NBand.M7300_7500.SplitData.node5239 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5240
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5238 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5239, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5238 : B5238.tree = HexagonCover.NBand.M7300_7500.SplitData.node5238 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5239
  · rfl

def B5237 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742542087917883600937189638208] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5238, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq5237 : B5237.tree = HexagonCover.NBand.M7300_7500.SplitData.node5237 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5238
  · rfl
  · rfl

def B5236 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5237]
theorem treeEq5236 : B5236.tree = HexagonCover.NBand.M7300_7500.SplitData.node5236 := by
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
  · exact treeEq5237

def B5235 : Block := .branch 78 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B5236, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq5235 : B5235.tree = HexagonCover.NBand.M7300_7500.SplitData.node5235 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5236
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5234 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![B5235, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq5234 : B5234.tree = HexagonCover.NBand.M7300_7500.SplitData.node5234 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5235
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5233 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5234]
theorem treeEq5233 : B5233.tree = HexagonCover.NBand.M7300_7500.SplitData.node5233 := by
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
  · exact treeEq5234

def B5232 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5233, (.leaf 0 [] 0)]
theorem treeEq5232 : B5232.tree = HexagonCover.NBand.M7300_7500.SplitData.node5232 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5233
  · rfl

def B5231 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5232, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5231 : B5231.tree = HexagonCover.NBand.M7300_7500.SplitData.node5231 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5232
  · rfl

def B5230 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5231, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq5230 : B5230.tree = HexagonCover.NBand.M7300_7500.SplitData.node5230 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5231
  · rfl
  · rfl

theorem accepted5230 : B5230.accepted = true := by decide +kernel
theorem checked5230 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5230 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496]) := by
  rw [← treeEq5230]
  exact B5230.sound accepted5230
#print axioms checked5230

def B5257 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5257 : B5257.tree = HexagonCover.NBand.M7300_7500.SplitData.node5257 := by
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

def B5256 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5257, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5256 : B5256.tree = HexagonCover.NBand.M7300_7500.SplitData.node5256 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5257
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5255 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5256, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5255 : B5255.tree = HexagonCover.NBand.M7300_7500.SplitData.node5255 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5256
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5254 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5255, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5254 : B5254.tree = HexagonCover.NBand.M7300_7500.SplitData.node5254 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5255
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5253 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5254, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5253 : B5253.tree = HexagonCover.NBand.M7300_7500.SplitData.node5253 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5254
  · rfl

def B5252 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5253, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5252 : B5252.tree = HexagonCover.NBand.M7300_7500.SplitData.node5252 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5253
  · rfl
  · rfl

def B5251 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5252]
theorem treeEq5251 : B5251.tree = HexagonCover.NBand.M7300_7500.SplitData.node5251 := by
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
  · exact treeEq5252

def B5250 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5251, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5250 : B5250.tree = HexagonCover.NBand.M7300_7500.SplitData.node5250 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5251
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5249 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5250]
theorem treeEq5249 : B5249.tree = HexagonCover.NBand.M7300_7500.SplitData.node5249 := by
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
  · exact treeEq5250

def B5248 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5249, (.leaf 0 [] 0)]
theorem treeEq5248 : B5248.tree = HexagonCover.NBand.M7300_7500.SplitData.node5248 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5249
  · rfl

def B5247 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5248, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5247 : B5247.tree = HexagonCover.NBand.M7300_7500.SplitData.node5247 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5248
  · rfl

def B5246 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5247, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5246 : B5246.tree = HexagonCover.NBand.M7300_7500.SplitData.node5246 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5247
  · rfl
  · rfl

def B5245 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5246]
theorem treeEq5245 : B5245.tree = HexagonCover.NBand.M7300_7500.SplitData.node5245 := by
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
  · exact treeEq5246

theorem accepted5245 : B5245.accepted = true := by decide +kernel
theorem checked5245 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5245 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5245]
  exact B5245.sound accepted5245
#print axioms checked5245

end HexagonCover.NBand.M7300_7500.SplitTree.Run0072
