import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0060
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B4278 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq4278 : B4278.tree = HexagonCover.NBand.M7300_7500.SplitData.node4278 := by
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

def B4277 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4278]
theorem treeEq4277 : B4277.tree = HexagonCover.NBand.M7300_7500.SplitData.node4277 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4278

def B4276 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B4277, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4276 : B4276.tree = HexagonCover.NBand.M7300_7500.SplitData.node4276 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4277
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4275 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4276]
theorem treeEq4275 : B4275.tree = HexagonCover.NBand.M7300_7500.SplitData.node4275 := by
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
  · exact treeEq4276

def B4274 : Block := .branch 169 ![2535301200456458802993406411137, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B4275, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4274 : B4274.tree = HexagonCover.NBand.M7300_7500.SplitData.node4274 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4275
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4273 : Block := .branch 170 ![2535301200456458802993406411137, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B4274, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4273 : B4273.tree = HexagonCover.NBand.M7300_7500.SplitData.node4273 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4274
  · rfl

def B4286 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 815).pointIds 815), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq4286 : B4286.tree = HexagonCover.NBand.M7300_7500.SplitData.node4286 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4285 : Block := .branch 100 ![385, 1461501637330902918204303802735925709793382106626, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![B4286, (.leaf 1 (Common.fact 941).pointIds 941), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq4285 : B4285.tree = HexagonCover.NBand.M7300_7500.SplitData.node4285 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4286
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4284 : Block := .branch 160 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 285).pointIds 285), B4285, (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq4284 : B4284.tree = HexagonCover.NBand.M7300_7500.SplitData.node4284 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4285
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4283 : Block := .branch 162 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B4284, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq4283 : B4283.tree = HexagonCover.NBand.M7300_7500.SplitData.node4283 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4284
  · rfl
  · rfl
  · rfl

def B4282 : Block := .branch 171 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B4283]
theorem treeEq4282 : B4282.tree = HexagonCover.NBand.M7300_7500.SplitData.node4282 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4283

def B4281 : Block := .branch 170 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4282, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4281 : B4281.tree = HexagonCover.NBand.M7300_7500.SplitData.node4281 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4282
  · rfl
  · rfl

def B4280 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4281, (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4280 : B4280.tree = HexagonCover.NBand.M7300_7500.SplitData.node4280 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4281
  · rfl

def B4279 : Block := .branch 168 ![2535301200456458802993406411137, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![B4280, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq4279 : B4279.tree = HexagonCover.NBand.M7300_7500.SplitData.node4279 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4280
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4272 : Block := .branch 108 ![2535301200456458802993406411137, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B4273, (.leaf 5 (Common.fact 308).pointIds 308), B4279]
theorem treeEq4272 : B4272.tree = HexagonCover.NBand.M7300_7500.SplitData.node4272 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4273
  · rfl
  · exact treeEq4279

theorem accepted4272 : B4272.accepted = true := by decide +kernel
theorem checked4272 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4272 (maskNeeds ![2535301200456458802993406411137, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq4272]
  exact B4272.sound accepted4272
#print axioms checked4272

def Tip4270_4272 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4272 ![2535301200456458802993406411137, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked4272
def B4294 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq4294 : B4294.tree = HexagonCover.NBand.M7300_7500.SplitData.node4294 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4293 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4294, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq4293 : B4293.tree = HexagonCover.NBand.M7300_7500.SplitData.node4293 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4294
  · rfl
  · rfl

def B4292 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4293]
theorem treeEq4292 : B4292.tree = HexagonCover.NBand.M7300_7500.SplitData.node4292 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4293

def B4291 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B4292, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4291 : B4291.tree = HexagonCover.NBand.M7300_7500.SplitData.node4291 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4292
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4290 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4291]
theorem treeEq4290 : B4290.tree = HexagonCover.NBand.M7300_7500.SplitData.node4290 := by
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
  · exact treeEq4291

def B4289 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B4290, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4289 : B4289.tree = HexagonCover.NBand.M7300_7500.SplitData.node4289 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4290
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4288 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4289, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4288 : B4288.tree = HexagonCover.NBand.M7300_7500.SplitData.node4288 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4289
  · rfl

def B4287 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4288, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq4287 : B4287.tree = HexagonCover.NBand.M7300_7500.SplitData.node4287 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4288
  · rfl
  · rfl

def B4271 : Block := .branch 101 ![2475880078570760549798248833, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![Tip4270_4272, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B4287]
theorem treeEq4271 : B4271.tree = HexagonCover.NBand.M7300_7500.SplitData.node4271 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4287

def B4302 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq4302 : B4302.tree = HexagonCover.NBand.M7300_7500.SplitData.node4302 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4301 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4302, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq4301 : B4301.tree = HexagonCover.NBand.M7300_7500.SplitData.node4301 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4302
  · rfl
  · rfl

def B4300 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4301]
theorem treeEq4300 : B4300.tree = HexagonCover.NBand.M7300_7500.SplitData.node4300 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4301

def B4299 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B4300, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4299 : B4299.tree = HexagonCover.NBand.M7300_7500.SplitData.node4299 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4300
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4298 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4299]
theorem treeEq4298 : B4298.tree = HexagonCover.NBand.M7300_7500.SplitData.node4298 := by
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
  · exact treeEq4299

def B4297 : Block := .branch 169 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B4298, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4297 : B4297.tree = HexagonCover.NBand.M7300_7500.SplitData.node4297 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4298
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4296 : Block := .branch 170 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4297, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4296 : B4296.tree = HexagonCover.NBand.M7300_7500.SplitData.node4296 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4297
  · rfl

def B4295 : Block := .branch 171 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4296, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq4295 : B4295.tree = HexagonCover.NBand.M7300_7500.SplitData.node4295 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4296
  · rfl
  · rfl

def B4270 : Block := .branch 91 ![385, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![B4271, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B4295]
theorem treeEq4270 : B4270.tree = HexagonCover.NBand.M7300_7500.SplitData.node4270 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4271
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4295

theorem accepted4270 : B4270.accepted = true := by decide +kernel
theorem checked4270 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4270 (maskNeeds ![385, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq4270]
  exact B4270.sound accepted4270
#print axioms checked4270

def Tip4268_4270 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4270 ![385, 618970019858862919563347458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked4270
def B4310 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq4310 : B4310.tree = HexagonCover.NBand.M7300_7500.SplitData.node4310 := by
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

def B4309 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B4310, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq4309 : B4309.tree = HexagonCover.NBand.M7300_7500.SplitData.node4309 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4310
  · rfl
  · rfl

def B4308 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4309]
theorem treeEq4308 : B4308.tree = HexagonCover.NBand.M7300_7500.SplitData.node4308 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4309

def B4307 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B4308, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4307 : B4307.tree = HexagonCover.NBand.M7300_7500.SplitData.node4307 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4308
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4306 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4307]
theorem treeEq4306 : B4306.tree = HexagonCover.NBand.M7300_7500.SplitData.node4306 := by
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
  · exact treeEq4307

def B4305 : Block := .branch 169 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B4306, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4305 : B4305.tree = HexagonCover.NBand.M7300_7500.SplitData.node4305 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4306
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4304 : Block := .branch 170 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4305, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4304 : B4304.tree = HexagonCover.NBand.M7300_7500.SplitData.node4304 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4305
  · rfl

def B4303 : Block := .branch 171 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891882809361521635045984960576] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4304, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq4303 : B4303.tree = HexagonCover.NBand.M7300_7500.SplitData.node4303 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4304
  · rfl
  · rfl

def B4269 : Block := .branch 89 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip4268_4270, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B4303]
theorem treeEq4269 : B4269.tree = HexagonCover.NBand.M7300_7500.SplitData.node4269 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4303

def B4318 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq4318 : B4318.tree = HexagonCover.NBand.M7300_7500.SplitData.node4318 := by
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

def B4317 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B4318, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq4317 : B4317.tree = HexagonCover.NBand.M7300_7500.SplitData.node4317 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4318
  · rfl
  · rfl

def B4316 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4317]
theorem treeEq4316 : B4316.tree = HexagonCover.NBand.M7300_7500.SplitData.node4316 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4317

def B4315 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516473233940747894922285678656] ![B4316, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq4315 : B4315.tree = HexagonCover.NBand.M7300_7500.SplitData.node4315 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4316
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4314 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4315]
theorem treeEq4314 : B4314.tree = HexagonCover.NBand.M7300_7500.SplitData.node4314 := by
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
  · exact treeEq4315

def B4313 : Block := .branch 169 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B4314, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4313 : B4313.tree = HexagonCover.NBand.M7300_7500.SplitData.node4313 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4314
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4312 : Block := .branch 170 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4313, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4312 : B4312.tree = HexagonCover.NBand.M7300_7500.SplitData.node4312 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4313
  · rfl

def B4311 : Block := .branch 171 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4312, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq4311 : B4311.tree = HexagonCover.NBand.M7300_7500.SplitData.node4311 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4312
  · rfl
  · rfl

def B4268 : Block := .branch 86 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 939).pointIds 939), B4269, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B4311]
theorem treeEq4268 : B4268.tree = HexagonCover.NBand.M7300_7500.SplitData.node4268 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4269
  · rfl
  · rfl
  · exact treeEq4311

theorem accepted4268 : B4268.accepted = true := by decide +kernel
theorem checked4268 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4268 (maskNeeds ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq4268]
  exact B4268.sound accepted4268
#print axioms checked4268

def Tip4265_4268 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4268 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked4268
def B4327 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 649037107316853453566312041250832, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 820).pointIds 820), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq4327 : B4327.tree = HexagonCover.NBand.M7300_7500.SplitData.node4327 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4326 : Block := .branch 109 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), B4327, (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 819).pointIds 819)]
theorem treeEq4326 : B4326.tree = HexagonCover.NBand.M7300_7500.SplitData.node4326 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4327
  · rfl
  · rfl

def B4325 : Block := .branch 124 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![B4326, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 818).pointIds 818)]
theorem treeEq4325 : B4325.tree = HexagonCover.NBand.M7300_7500.SplitData.node4325 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4326
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4324 : Block := .branch 160 ![385, 302821822771610037257730, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B4325]
theorem treeEq4324 : B4324.tree = HexagonCover.NBand.M7300_7500.SplitData.node4324 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4325

def B4323 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231526961251331606018, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 753).pointIds 753), B4324, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq4323 : B4323.tree = HexagonCover.NBand.M7300_7500.SplitData.node4323 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4324
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4322 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231526961251331606018, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4323]
theorem treeEq4322 : B4322.tree = HexagonCover.NBand.M7300_7500.SplitData.node4322 := by
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
  · exact treeEq4323

def B4321 : Block := .branch 169 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B4322, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq4321 : B4321.tree = HexagonCover.NBand.M7300_7500.SplitData.node4321 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4322
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4320 : Block := .branch 170 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891265048267698559537710104640] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4321, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4320 : B4320.tree = HexagonCover.NBand.M7300_7500.SplitData.node4320 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4321
  · rfl

def B4319 : Block := .branch 171 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891265048267698559537710104640] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4320, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq4319 : B4319.tree = HexagonCover.NBand.M7300_7500.SplitData.node4319 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4320
  · rfl
  · rfl

def B4267 : Block := .branch 80 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![Tip4265_4268, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B4319]
theorem treeEq4267 : B4267.tree = HexagonCover.NBand.M7300_7500.SplitData.node4267 := by
  change Tree.branch (80 : Fin 172) _ = Tree.branch (80 : Fin 172) _
  apply congrArg (Tree.branch (80 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4319

def B4266 : Block := .branch 149 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B4267, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq4266 : B4266.tree = HexagonCover.NBand.M7300_7500.SplitData.node4266 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4267
  · rfl
  · rfl

def B4265 : Block := .branch 88 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1012).pointIds 1012), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4266]
theorem treeEq4265 : B4265.tree = HexagonCover.NBand.M7300_7500.SplitData.node4265 := by
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
  · exact treeEq4266

theorem accepted4265 : B4265.accepted = true := by decide +kernel
theorem checked4265 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4265 (maskNeeds ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4265]
  exact B4265.sound accepted4265
#print axioms checked4265

def B4350 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275488515612336070444184981120785753571392] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 679).pointIds 679), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq4350 : B4350.tree = HexagonCover.NBand.M7300_7500.SplitData.node4350 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4349 : Block := .branch 124 ![10385861367669883486462489361645953, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 825).pointIds 825), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B4350]
theorem treeEq4349 : B4349.tree = HexagonCover.NBand.M7300_7500.SplitData.node4349 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4350

def B4348 : Block := .branch 100 ![10384593717069655257060992658440577, 1461501637330902918203684833011430924835285370370, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B4349, (.leaf 1 (Common.fact 946).pointIds 946), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq4348 : B4348.tree = HexagonCover.NBand.M7300_7500.SplitData.node4348 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4349
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4347 : Block := .branch 160 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 285).pointIds 285), B4348, (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq4347 : B4347.tree = HexagonCover.NBand.M7300_7500.SplitData.node4347 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4348
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4346 : Block := .branch 75 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B4347, (.leaf 3 (Common.fact 662).pointIds 662), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq4346 : B4346.tree = HexagonCover.NBand.M7300_7500.SplitData.node4346 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4347
  · rfl
  · rfl
  · rfl
  · rfl

def B4345 : Block := .branch 162 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B4346, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq4345 : B4345.tree = HexagonCover.NBand.M7300_7500.SplitData.node4345 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4346
  · rfl
  · rfl
  · rfl

def B4344 : Block := .branch 168 ![10384593717069655257060992658440577, 295364077961466611202, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B4345, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq4344 : B4344.tree = HexagonCover.NBand.M7300_7500.SplitData.node4344 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4345
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4343 : Block := .branch 171 ![10384593717069655257060992658440577, 295364077961466611202, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B4344]
theorem treeEq4343 : B4343.tree = HexagonCover.NBand.M7300_7500.SplitData.node4343 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4344

def B4342 : Block := .branch 170 ![10384593717069655257060992658440577, 295364077961466611202, 18446745173221185540, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4343, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4342 : B4342.tree = HexagonCover.NBand.M7300_7500.SplitData.node4342 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4343
  · rfl
  · rfl

def B4341 : Block := .branch 169 ![10384593717070245552871351364092289, 295364077961466611202, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), B4342, (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq4341 : B4341.tree = HexagonCover.NBand.M7300_7500.SplitData.node4341 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4342
  · rfl

theorem accepted4341 : B4341.accepted = true := by decide +kernel
theorem checked4341 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4341 (maskNeeds ![10384593717070245552871351364092289, 295364077961466611202, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq4341]
  exact B4341.sound accepted4341
#print axioms checked4341

end HexagonCover.NBand.M7300_7500.SplitTree.Run0060
