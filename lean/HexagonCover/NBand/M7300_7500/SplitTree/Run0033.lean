import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0033
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B2348 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq2348 : B2348.tree = HexagonCover.NBand.M7300_7500.SplitData.node2348 := by
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

def B2347 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2348]
theorem treeEq2347 : B2347.tree = HexagonCover.NBand.M7300_7500.SplitData.node2347 := by
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
  · exact treeEq2348

def B2346 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2347, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2346 : B2346.tree = HexagonCover.NBand.M7300_7500.SplitData.node2346 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2347
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2345 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2346]
theorem treeEq2345 : B2345.tree = HexagonCover.NBand.M7300_7500.SplitData.node2345 := by
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
  · exact treeEq2346

def B2344 : Block := .branch 169 ![2535301200456458802993406411137, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2345, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2344 : B2344.tree = HexagonCover.NBand.M7300_7500.SplitData.node2344 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2345
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2343 : Block := .branch 170 ![2535301200456458802993406411137, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B2344, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2343 : B2343.tree = HexagonCover.NBand.M7300_7500.SplitData.node2343 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2344
  · rfl

def B2356 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 815).pointIds 815), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq2356 : B2356.tree = HexagonCover.NBand.M7300_7500.SplitData.node2356 := by
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

def B2355 : Block := .branch 100 ![385, 1461501637330902918204303802735925710892893734402, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![B2356, (.leaf 1 (Common.fact 432).pointIds 432), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq2355 : B2355.tree = HexagonCover.NBand.M7300_7500.SplitData.node2355 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2356
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2354 : Block := .branch 160 ![385, 618970019642691236961191426, 18518801667747485700, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 285).pointIds 285), B2355, (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq2354 : B2354.tree = HexagonCover.NBand.M7300_7500.SplitData.node2354 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2355
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2353 : Block := .branch 162 ![385, 618970019642691236961191426, 18518801667747485700, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B2354, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq2353 : B2353.tree = HexagonCover.NBand.M7300_7500.SplitData.node2353 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2354
  · rfl
  · rfl
  · rfl

def B2352 : Block := .branch 171 ![385, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2353]
theorem treeEq2352 : B2352.tree = HexagonCover.NBand.M7300_7500.SplitData.node2352 := by
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
  · exact treeEq2353

def B2351 : Block := .branch 170 ![385, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2352, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2351 : B2351.tree = HexagonCover.NBand.M7300_7500.SplitData.node2351 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2352
  · rfl
  · rfl

def B2350 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2351, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2350 : B2350.tree = HexagonCover.NBand.M7300_7500.SplitData.node2350 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2351
  · rfl

def B2349 : Block := .branch 168 ![2535301200456458802993406411137, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B2350, (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq2349 : B2349.tree = HexagonCover.NBand.M7300_7500.SplitData.node2349 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2350
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2342 : Block := .branch 108 ![2535301200456458802993406411137, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B2343, (.leaf 5 (Common.fact 308).pointIds 308), B2349]
theorem treeEq2342 : B2342.tree = HexagonCover.NBand.M7300_7500.SplitData.node2342 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2343
  · rfl
  · exact treeEq2349

theorem accepted2342 : B2342.accepted = true := by decide +kernel
theorem checked2342 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2342 (maskNeeds ![2535301200456458802993406411137, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2342]
  exact B2342.sound accepted2342
#print axioms checked2342

def Tip2340_2342 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2342 ![2535301200456458802993406411137, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2342
def B2364 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq2364 : B2364.tree = HexagonCover.NBand.M7300_7500.SplitData.node2364 := by
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

def B2363 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2364, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq2363 : B2363.tree = HexagonCover.NBand.M7300_7500.SplitData.node2363 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2364
  · rfl
  · rfl

def B2362 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2363]
theorem treeEq2362 : B2362.tree = HexagonCover.NBand.M7300_7500.SplitData.node2362 := by
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
  · exact treeEq2363

def B2361 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B2362, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2361 : B2361.tree = HexagonCover.NBand.M7300_7500.SplitData.node2361 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2362
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2360 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2361]
theorem treeEq2360 : B2360.tree = HexagonCover.NBand.M7300_7500.SplitData.node2360 := by
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
  · exact treeEq2361

def B2359 : Block := .branch 169 ![2475880078570760549798248833, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B2360, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2359 : B2359.tree = HexagonCover.NBand.M7300_7500.SplitData.node2359 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2360
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2358 : Block := .branch 170 ![2475880078570760549798248833, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2359, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2358 : B2358.tree = HexagonCover.NBand.M7300_7500.SplitData.node2358 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2359
  · rfl

def B2357 : Block := .branch 171 ![2475880078570760549798248833, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2358, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq2357 : B2357.tree = HexagonCover.NBand.M7300_7500.SplitData.node2357 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2358
  · rfl
  · rfl

def B2341 : Block := .branch 101 ![2475880078570760549798248833, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip2340_2342, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B2357]
theorem treeEq2341 : B2341.tree = HexagonCover.NBand.M7300_7500.SplitData.node2341 := by
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
  · exact treeEq2357

def B2372 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2372 : B2372.tree = HexagonCover.NBand.M7300_7500.SplitData.node2372 := by
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

def B2371 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2372, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2371 : B2371.tree = HexagonCover.NBand.M7300_7500.SplitData.node2371 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2372
  · rfl
  · rfl

def B2370 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2371]
theorem treeEq2370 : B2370.tree = HexagonCover.NBand.M7300_7500.SplitData.node2370 := by
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
  · exact treeEq2371

def B2369 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B2370, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2369 : B2369.tree = HexagonCover.NBand.M7300_7500.SplitData.node2369 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2370
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2368 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2369]
theorem treeEq2368 : B2368.tree = HexagonCover.NBand.M7300_7500.SplitData.node2368 := by
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
  · exact treeEq2369

def B2367 : Block := .branch 169 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B2368, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2367 : B2367.tree = HexagonCover.NBand.M7300_7500.SplitData.node2367 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2368
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2366 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2367, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2366 : B2366.tree = HexagonCover.NBand.M7300_7500.SplitData.node2366 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2367
  · rfl

def B2365 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2366, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq2365 : B2365.tree = HexagonCover.NBand.M7300_7500.SplitData.node2365 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2366
  · rfl
  · rfl

def B2340 : Block := .branch 91 ![385, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B2341, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B2365]
theorem treeEq2340 : B2340.tree = HexagonCover.NBand.M7300_7500.SplitData.node2340 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2341
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2365

theorem accepted2340 : B2340.accepted = true := by decide +kernel
theorem checked2340 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2340 (maskNeeds ![385, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2340]
  exact B2340.sound accepted2340
#print axioms checked2340

def Tip2338_2340 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2340 ![385, 618970019786947162525402626, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2340
def B2380 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq2380 : B2380.tree = HexagonCover.NBand.M7300_7500.SplitData.node2380 := by
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

def B2379 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2380, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq2379 : B2379.tree = HexagonCover.NBand.M7300_7500.SplitData.node2379 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2380
  · rfl
  · rfl

def B2378 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2379]
theorem treeEq2378 : B2378.tree = HexagonCover.NBand.M7300_7500.SplitData.node2378 := by
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
  · exact treeEq2379

def B2377 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2378, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2377 : B2377.tree = HexagonCover.NBand.M7300_7500.SplitData.node2377 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2378
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2376 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2377]
theorem treeEq2376 : B2376.tree = HexagonCover.NBand.M7300_7500.SplitData.node2376 := by
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
  · exact treeEq2377

def B2375 : Block := .branch 169 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2376, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2375 : B2375.tree = HexagonCover.NBand.M7300_7500.SplitData.node2375 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2376
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2374 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2375, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2374 : B2374.tree = HexagonCover.NBand.M7300_7500.SplitData.node2374 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2375
  · rfl

def B2373 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2374, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq2373 : B2373.tree = HexagonCover.NBand.M7300_7500.SplitData.node2373 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2374
  · rfl
  · rfl

def B2339 : Block := .branch 89 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip2338_2340, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B2373]
theorem treeEq2339 : B2339.tree = HexagonCover.NBand.M7300_7500.SplitData.node2339 := by
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
  · exact treeEq2373

def B2388 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq2388 : B2388.tree = HexagonCover.NBand.M7300_7500.SplitData.node2388 := by
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

def B2387 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2388, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq2387 : B2387.tree = HexagonCover.NBand.M7300_7500.SplitData.node2387 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2388
  · rfl
  · rfl

def B2386 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2387]
theorem treeEq2386 : B2386.tree = HexagonCover.NBand.M7300_7500.SplitData.node2386 := by
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
  · exact treeEq2387

def B2385 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B2386, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2385 : B2385.tree = HexagonCover.NBand.M7300_7500.SplitData.node2385 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2386
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2384 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2385]
theorem treeEq2384 : B2384.tree = HexagonCover.NBand.M7300_7500.SplitData.node2384 := by
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
  · exact treeEq2385

def B2383 : Block := .branch 169 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B2384, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2383 : B2383.tree = HexagonCover.NBand.M7300_7500.SplitData.node2383 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2384
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2382 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2383, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2382 : B2382.tree = HexagonCover.NBand.M7300_7500.SplitData.node2382 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2383
  · rfl

def B2381 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2382, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq2381 : B2381.tree = HexagonCover.NBand.M7300_7500.SplitData.node2381 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2382
  · rfl
  · rfl

def B2338 : Block := .branch 86 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B2339, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B2381]
theorem treeEq2338 : B2338.tree = HexagonCover.NBand.M7300_7500.SplitData.node2338 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2339
  · rfl
  · rfl
  · exact treeEq2381

theorem accepted2338 : B2338.accepted = true := by decide +kernel
theorem checked2338 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2338 (maskNeeds ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2338]
  exact B2338.sound accepted2338
#print axioms checked2338

def B2419 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275488515612336070444184981120785753571392] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 679).pointIds 679), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq2419 : B2419.tree = HexagonCover.NBand.M7300_7500.SplitData.node2419 := by
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

def B2418 : Block := .branch 124 ![10385861367669883486462489361645953, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 825).pointIds 825), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2419]
theorem treeEq2418 : B2418.tree = HexagonCover.NBand.M7300_7500.SplitData.node2418 := by
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
  · exact treeEq2419

def B2417 : Block := .branch 100 ![10384593717069655257060992658440577, 1461501637330902918203684833011430925934796998146, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B2418, (.leaf 1 (Common.fact 823).pointIds 823), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq2417 : B2417.tree = HexagonCover.NBand.M7300_7500.SplitData.node2417 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2418
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2416 : Block := .branch 160 ![10384593717069655257060992658440577, 295147906278864455170, 18518801667747485700, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 285).pointIds 285), B2417, (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq2416 : B2416.tree = HexagonCover.NBand.M7300_7500.SplitData.node2416 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2417
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2415 : Block := .branch 75 ![10384593717069655257060992658440577, 295147906278864455170, 18518801667747485700, 5846006549323611672814778016491359746757320794120, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B2416, (.leaf 3 (Common.fact 662).pointIds 662), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2415 : B2415.tree = HexagonCover.NBand.M7300_7500.SplitData.node2415 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2416
  · rfl
  · rfl
  · rfl
  · rfl

def B2414 : Block := .branch 162 ![10384593717069655257060992658440577, 295147906278864455170, 18518801667747485700, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B2415, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq2414 : B2414.tree = HexagonCover.NBand.M7300_7500.SplitData.node2414 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2415
  · rfl
  · rfl
  · rfl

def B2413 : Block := .branch 168 ![10384593717069655257060992658440577, 295292162204428666370, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 2993155353275467247964403511790218520207821268058176] ![B2414, (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2413 : B2413.tree = HexagonCover.NBand.M7300_7500.SplitData.node2413 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2414
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2412 : Block := .branch 171 ![10384593717069655257060992658440577, 295292162204428666370, 18518801667747485700, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2413]
theorem treeEq2412 : B2412.tree = HexagonCover.NBand.M7300_7500.SplitData.node2412 := by
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
  · exact treeEq2413

def B2411 : Block := .branch 170 ![10384593717069655257060992658440577, 295292162204428666370, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2412, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2411 : B2411.tree = HexagonCover.NBand.M7300_7500.SplitData.node2411 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2412
  · rfl
  · rfl

def B2410 : Block := .branch 169 ![10384593717070245552871351364092289, 295292162204428666370, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2411, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2410 : B2410.tree = HexagonCover.NBand.M7300_7500.SplitData.node2410 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2411
  · rfl

theorem accepted2410 : B2410.accepted = true := by decide +kernel
theorem checked2410 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2410 (maskNeeds ![10384593717070245552871351364092289, 295292162204428666370, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2410]
  exact B2410.sound accepted2410
#print axioms checked2410

def Tip2409_2410 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2410 ![10384593717070245552871351364092289, 295292162204428666370, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2410
def B2429 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq2429 : B2429.tree = HexagonCover.NBand.M7300_7500.SplitData.node2429 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2428 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2429, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq2428 : B2428.tree = HexagonCover.NBand.M7300_7500.SplitData.node2428 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2429
  · rfl
  · rfl

def B2427 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2428]
theorem treeEq2427 : B2427.tree = HexagonCover.NBand.M7300_7500.SplitData.node2427 := by
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
  · exact treeEq2428

def B2426 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B2427, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2426 : B2426.tree = HexagonCover.NBand.M7300_7500.SplitData.node2426 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2427
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2425 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 828).pointIds 828), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B2426]
theorem treeEq2425 : B2425.tree = HexagonCover.NBand.M7300_7500.SplitData.node2425 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2426

def B2424 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2425]
theorem treeEq2424 : B2424.tree = HexagonCover.NBand.M7300_7500.SplitData.node2424 := by
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
  · exact treeEq2425

def B2423 : Block := .branch 169 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B2424, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2423 : B2423.tree = HexagonCover.NBand.M7300_7500.SplitData.node2423 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2424
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2422 : Block := .branch 170 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2423, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2422 : B2422.tree = HexagonCover.NBand.M7300_7500.SplitData.node2422 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2423
  · rfl

def B2421 : Block := .branch 171 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2422, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq2421 : B2421.tree = HexagonCover.NBand.M7300_7500.SplitData.node2421 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2422
  · rfl
  · rfl

def B2420 : Block := .branch 160 ![2475880078570760549798248833, 738014019973457905154, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 827).pointIds 827), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2421]
theorem treeEq2420 : B2420.tree = HexagonCover.NBand.M7300_7500.SplitData.node2420 := by
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
  · exact treeEq2421

def B2409 : Block := .branch 69 ![10384596192949733827821542456689025, 442866114794105079298, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip2409_2410, B2420, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2409 : B2409.tree = HexagonCover.NBand.M7300_7500.SplitData.node2409 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2420
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2409 : B2409.accepted = true := by decide +kernel
theorem checked2409 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2409 (maskNeeds ![10384596192949733827821542456689025, 442866114794105079298, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2409]
  exact B2409.sound accepted2409
#print axioms checked2409

end HexagonCover.NBand.M7300_7500.SplitTree.Run0033
