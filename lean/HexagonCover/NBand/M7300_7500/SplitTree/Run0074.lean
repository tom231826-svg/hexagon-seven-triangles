import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0072
import HexagonCover.NBand.M7300_7500.SplitTree.Run0073
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0074
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip5280_5282 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5282 ![385, 302231599018845369533954, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0073.checked5282
def Tip5280_5303 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5303 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0073.checked5303
def B5302 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5302 : B5302.tree = HexagonCover.NBand.M7300_7500.SplitData.node5302 := by
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

def B5301 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5302, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5301 : B5301.tree = HexagonCover.NBand.M7300_7500.SplitData.node5301 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5302
  · rfl
  · rfl

def B5300 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5301, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5300 : B5300.tree = HexagonCover.NBand.M7300_7500.SplitData.node5300 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5301
  · rfl

def B5299 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5300, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5299 : B5299.tree = HexagonCover.NBand.M7300_7500.SplitData.node5299 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5300
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5298 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5299]
theorem treeEq5298 : B5298.tree = HexagonCover.NBand.M7300_7500.SplitData.node5298 := by
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
  · exact treeEq5299

def B5297 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5298, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5297 : B5297.tree = HexagonCover.NBand.M7300_7500.SplitData.node5297 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5298
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5296 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5297, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5296 : B5296.tree = HexagonCover.NBand.M7300_7500.SplitData.node5296 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5297
  · rfl

def B5295 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5296, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5295 : B5295.tree = HexagonCover.NBand.M7300_7500.SplitData.node5295 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5296
  · rfl
  · rfl

def B5281 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5280_5282, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5295]
theorem treeEq5281 : B5281.tree = HexagonCover.NBand.M7300_7500.SplitData.node5281 := by
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
  · exact treeEq5295

def B5280 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5281, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5280_5303]
theorem treeEq5280 : B5280.tree = HexagonCover.NBand.M7300_7500.SplitData.node5280 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5281
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5280 : B5280.accepted = true := by decide +kernel
theorem checked5280 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5280 (maskNeeds ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5280]
  exact B5280.sound accepted5280
#print axioms checked5280

def Tip5206_5245 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5245 ![385, 302231599018845369533954, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0072.checked5245
def Tip5206_5266 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5266 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0073.checked5266
def Tip5206_5207 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5207 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0073.checked5207
def B5265 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5265 : B5265.tree = HexagonCover.NBand.M7300_7500.SplitData.node5265 := by
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

def B5264 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5265, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5264 : B5264.tree = HexagonCover.NBand.M7300_7500.SplitData.node5264 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5265
  · rfl
  · rfl

def B5263 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5264, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5263 : B5263.tree = HexagonCover.NBand.M7300_7500.SplitData.node5263 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5264
  · rfl

def B5262 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5263, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5262 : B5262.tree = HexagonCover.NBand.M7300_7500.SplitData.node5262 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5263
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5261 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5262]
theorem treeEq5261 : B5261.tree = HexagonCover.NBand.M7300_7500.SplitData.node5261 := by
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
  · exact treeEq5262

def B5260 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5261, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5260 : B5260.tree = HexagonCover.NBand.M7300_7500.SplitData.node5260 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5261
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5259 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5260, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5259 : B5259.tree = HexagonCover.NBand.M7300_7500.SplitData.node5259 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5260
  · rfl

def B5258 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5259, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5258 : B5258.tree = HexagonCover.NBand.M7300_7500.SplitData.node5258 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5259
  · rfl
  · rfl

def B5244 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5206_5245, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5258]
theorem treeEq5244 : B5244.tree = HexagonCover.NBand.M7300_7500.SplitData.node5244 := by
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
  · exact treeEq5258

def B5243 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5244, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5206_5266]
theorem treeEq5243 : B5243.tree = HexagonCover.NBand.M7300_7500.SplitData.node5243 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5244
  · rfl
  · rfl
  · rfl
  · rfl

def B5206 : Block := .branch 74 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip5206_5207, B5243, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq5206 : B5206.tree = HexagonCover.NBand.M7300_7500.SplitData.node5206 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5243
  · rfl
  · rfl
  · rfl

theorem accepted5206 : B5206.accepted = true := by decide +kernel
theorem checked5206 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5206 (maskNeeds ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5206]
  exact B5206.sound accepted5206
#print axioms checked5206

def Tip5205_5318 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5318 ![385, 302231599018845369533954, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0073.checked5318
def Tip5205_5339 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5339 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] HexagonCover.NBand.M7300_7500.SplitTree.Run0073.checked5339
def Tip5205_5280 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5280 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked5280
def Tip5205_5206 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5206 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked5206
def B5338 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq5338 : B5338.tree = HexagonCover.NBand.M7300_7500.SplitData.node5338 := by
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

def B5337 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5338, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5337 : B5337.tree = HexagonCover.NBand.M7300_7500.SplitData.node5337 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5338
  · rfl
  · rfl

def B5336 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5337, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5336 : B5336.tree = HexagonCover.NBand.M7300_7500.SplitData.node5336 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5337
  · rfl

def B5335 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5336, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq5335 : B5335.tree = HexagonCover.NBand.M7300_7500.SplitData.node5335 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5336
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5334 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5335]
theorem treeEq5334 : B5334.tree = HexagonCover.NBand.M7300_7500.SplitData.node5334 := by
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
  · exact treeEq5335

def B5333 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B5334, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq5333 : B5333.tree = HexagonCover.NBand.M7300_7500.SplitData.node5333 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5334
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5332 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5333, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5332 : B5332.tree = HexagonCover.NBand.M7300_7500.SplitData.node5332 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5333
  · rfl

def B5331 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5332, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq5331 : B5331.tree = HexagonCover.NBand.M7300_7500.SplitData.node5331 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5332
  · rfl
  · rfl

def B5317 : Block := .branch 78 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), Tip5205_5318, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B5331]
theorem treeEq5317 : B5317.tree = HexagonCover.NBand.M7300_7500.SplitData.node5317 := by
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
  · exact treeEq5331

def B5316 : Block := .branch 76 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B5317, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), Tip5205_5339]
theorem treeEq5316 : B5316.tree = HexagonCover.NBand.M7300_7500.SplitData.node5316 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5317
  · rfl
  · rfl
  · rfl
  · rfl

def B5279 : Block := .branch 74 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip5205_5280, B5316, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq5279 : B5279.tree = HexagonCover.NBand.M7300_7500.SplitData.node5279 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5316
  · rfl
  · rfl
  · rfl

def B5205 : Block := .branch 73 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip5205_5206, B5279, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq5205 : B5205.tree = HexagonCover.NBand.M7300_7500.SplitData.node5205 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5279
  · rfl
  · rfl
  · rfl

theorem accepted5205 : B5205.accepted = true := by decide +kernel
theorem checked5205 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5205 (maskNeeds ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5205]
  exact B5205.sound accepted5205
#print axioms checked5205

def Tip4923_5115 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5115 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0072.checked5115
def Tip4923_4924 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4924 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0072.checked4924
def B5196 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1031).pointIds 1031)]
theorem treeEq5196 : B5196.tree = HexagonCover.NBand.M7300_7500.SplitData.node5196 := by
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

def B5195 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5196, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5195 : B5195.tree = HexagonCover.NBand.M7300_7500.SplitData.node5195 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5196
  · rfl
  · rfl

def B5194 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5195, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5194 : B5194.tree = HexagonCover.NBand.M7300_7500.SplitData.node5194 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5195
  · rfl

def B5193 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![B5194, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq5193 : B5193.tree = HexagonCover.NBand.M7300_7500.SplitData.node5193 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5194
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5192 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 723).pointIds 723), B5193, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq5192 : B5192.tree = HexagonCover.NBand.M7300_7500.SplitData.node5192 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5193
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5191 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5192]
theorem treeEq5191 : B5191.tree = HexagonCover.NBand.M7300_7500.SplitData.node5191 := by
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
  · exact treeEq5192

def B5190 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![B5191, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq5190 : B5190.tree = HexagonCover.NBand.M7300_7500.SplitData.node5190 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5191
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5189 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5190, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5189 : B5189.tree = HexagonCover.NBand.M7300_7500.SplitData.node5189 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5190
  · rfl

def B5188 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5189, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq5188 : B5188.tree = HexagonCover.NBand.M7300_7500.SplitData.node5188 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5189
  · rfl
  · rfl

def B5114 : Block := .branch 68 ![10384596192949733827821542456689025, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip4923_5115, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B5188]
theorem treeEq5114 : B5114.tree = HexagonCover.NBand.M7300_7500.SplitData.node5114 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5188

def B5113 : Block := .branch 91 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B5114, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq5113 : B5113.tree = HexagonCover.NBand.M7300_7500.SplitData.node5113 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5114
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5112 : Block := .branch 113 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B5113, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq5112 : B5112.tree = HexagonCover.NBand.M7300_7500.SplitData.node5112 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5113
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5111 : Block := .branch 135 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B5112, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq5111 : B5111.tree = HexagonCover.NBand.M7300_7500.SplitData.node5111 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5112
  · rfl

def B5110 : Block := .branch 138 ![385, 144115188075857410, 18446745173221185540, 79266857585224971466424999944, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B5111, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq5110 : B5110.tree = HexagonCover.NBand.M7300_7500.SplitData.node5110 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5111
  · rfl
  · rfl

def B5109 : Block := .branch 144 ![385, 144115188075857410, 18446745173221185540, 79266857585224971466424999944, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B5110, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq5109 : B5109.tree = HexagonCover.NBand.M7300_7500.SplitData.node5109 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5110
  · rfl

def B5108 : Block := .branch 149 ![385, 144115188075857410, 18446745173221185540, 79266857585224971466424999944, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B5109, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq5108 : B5108.tree = HexagonCover.NBand.M7300_7500.SplitData.node5108 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5109
  · rfl
  · rfl

def B5107 : Block := .branch 161 ![385, 144115188075857410, 18446745173221185540, 79266857585224971466424999944, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B5108]
theorem treeEq5107 : B5107.tree = HexagonCover.NBand.M7300_7500.SplitData.node5107 := by
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
  · exact treeEq5108

def B4923 : Block := .branch 73 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip4923_4924, B5107, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq4923 : B4923.tree = HexagonCover.NBand.M7300_7500.SplitData.node4923 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5107
  · rfl
  · rfl
  · rfl

theorem accepted4923 : B4923.accepted = true := by decide +kernel
theorem checked4923 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4923 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4923]
  exact B4923.sound accepted4923
#print axioms checked4923

def B5386 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5386 : B5386.tree = HexagonCover.NBand.M7300_7500.SplitData.node5386 := by
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

def B5385 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5386, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5385 : B5385.tree = HexagonCover.NBand.M7300_7500.SplitData.node5385 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5386
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5384 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5385, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5384 : B5384.tree = HexagonCover.NBand.M7300_7500.SplitData.node5384 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5385
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5383 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5384, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5383 : B5383.tree = HexagonCover.NBand.M7300_7500.SplitData.node5383 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5384
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5382 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5383, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5382 : B5382.tree = HexagonCover.NBand.M7300_7500.SplitData.node5382 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5383
  · rfl

def B5381 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5382, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5381 : B5381.tree = HexagonCover.NBand.M7300_7500.SplitData.node5381 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5382
  · rfl
  · rfl

def B5380 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5381]
theorem treeEq5380 : B5380.tree = HexagonCover.NBand.M7300_7500.SplitData.node5380 := by
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
  · exact treeEq5381

def B5379 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5380, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5379 : B5379.tree = HexagonCover.NBand.M7300_7500.SplitData.node5379 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5380
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5378 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5379]
theorem treeEq5378 : B5378.tree = HexagonCover.NBand.M7300_7500.SplitData.node5378 := by
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
  · exact treeEq5379

def B5377 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5378, (.leaf 0 [] 0)]
theorem treeEq5377 : B5377.tree = HexagonCover.NBand.M7300_7500.SplitData.node5377 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5378
  · rfl

def B5376 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5377, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5376 : B5376.tree = HexagonCover.NBand.M7300_7500.SplitData.node5376 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5377
  · rfl

def B5375 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5376, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5375 : B5375.tree = HexagonCover.NBand.M7300_7500.SplitData.node5375 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5376
  · rfl
  · rfl

def B5374 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5375]
theorem treeEq5374 : B5374.tree = HexagonCover.NBand.M7300_7500.SplitData.node5374 := by
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
  · exact treeEq5375

theorem accepted5374 : B5374.accepted = true := by decide +kernel
theorem checked5374 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5374 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5374]
  exact B5374.sound accepted5374
#print axioms checked5374

def B5407 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq5407 : B5407.tree = HexagonCover.NBand.M7300_7500.SplitData.node5407 := by
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

def B5406 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5407, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq5406 : B5406.tree = HexagonCover.NBand.M7300_7500.SplitData.node5406 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5407
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5405 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![(.leaf 0 (Common.fact 906).pointIds 906), B5406, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq5405 : B5405.tree = HexagonCover.NBand.M7300_7500.SplitData.node5405 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5406
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5404 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5405, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq5404 : B5404.tree = HexagonCover.NBand.M7300_7500.SplitData.node5404 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5405
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5403 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5404, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5403 : B5403.tree = HexagonCover.NBand.M7300_7500.SplitData.node5403 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5404
  · rfl

def B5402 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742542087917883600937189638208] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5403, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq5402 : B5402.tree = HexagonCover.NBand.M7300_7500.SplitData.node5402 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5403
  · rfl
  · rfl

def B5401 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5402]
theorem treeEq5401 : B5401.tree = HexagonCover.NBand.M7300_7500.SplitData.node5401 := by
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
  · exact treeEq5402

def B5400 : Block := .branch 78 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B5401, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq5400 : B5400.tree = HexagonCover.NBand.M7300_7500.SplitData.node5400 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5401
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5399 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![B5400, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq5399 : B5399.tree = HexagonCover.NBand.M7300_7500.SplitData.node5399 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5400
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5398 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5399]
theorem treeEq5398 : B5398.tree = HexagonCover.NBand.M7300_7500.SplitData.node5398 := by
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
  · exact treeEq5399

def B5397 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5398, (.leaf 0 [] 0)]
theorem treeEq5397 : B5397.tree = HexagonCover.NBand.M7300_7500.SplitData.node5397 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5398
  · rfl

def B5396 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5397, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5396 : B5396.tree = HexagonCover.NBand.M7300_7500.SplitData.node5396 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5397
  · rfl

def B5395 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5396, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq5395 : B5395.tree = HexagonCover.NBand.M7300_7500.SplitData.node5395 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5396
  · rfl
  · rfl

theorem accepted5395 : B5395.accepted = true := by decide +kernel
theorem checked5395 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5395 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496]) := by
  rw [← treeEq5395]
  exact B5395.sound accepted5395
#print axioms checked5395

end HexagonCover.NBand.M7300_7500.SplitTree.Run0074
