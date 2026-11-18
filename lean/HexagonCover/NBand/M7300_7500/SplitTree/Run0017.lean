import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0017
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B1253 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq1253 : B1253.tree = HexagonCover.NBand.M7300_7500.SplitData.node1253 := by
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

def B1252 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1253]
theorem treeEq1252 : B1252.tree = HexagonCover.NBand.M7300_7500.SplitData.node1252 := by
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
  · exact treeEq1253

def B1251 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B1252, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1251 : B1251.tree = HexagonCover.NBand.M7300_7500.SplitData.node1251 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1252
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1250 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1251]
theorem treeEq1250 : B1250.tree = HexagonCover.NBand.M7300_7500.SplitData.node1250 := by
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
  · exact treeEq1251

def B1249 : Block := .branch 169 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B1250, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1249 : B1249.tree = HexagonCover.NBand.M7300_7500.SplitData.node1249 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1250
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1248 : Block := .branch 170 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 679).pointIds 679), B1249, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1248 : B1248.tree = HexagonCover.NBand.M7300_7500.SplitData.node1248 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1249
  · rfl

def B1258 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq1258 : B1258.tree = HexagonCover.NBand.M7300_7500.SplitData.node1258 := by
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
  · rfl

def B1257 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B1258]
theorem treeEq1257 : B1257.tree = HexagonCover.NBand.M7300_7500.SplitData.node1257 := by
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
  · exact treeEq1258

def B1256 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), B1257, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1256 : B1256.tree = HexagonCover.NBand.M7300_7500.SplitData.node1256 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1257
  · rfl
  · rfl

def B1255 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B1256, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1255 : B1255.tree = HexagonCover.NBand.M7300_7500.SplitData.node1255 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1256
  · rfl

def B1254 : Block := .branch 168 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B1255, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq1254 : B1254.tree = HexagonCover.NBand.M7300_7500.SplitData.node1254 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1255
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1247 : Block := .branch 108 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B1248, (.leaf 5 (Common.fact 308).pointIds 308), B1254]
theorem treeEq1247 : B1247.tree = HexagonCover.NBand.M7300_7500.SplitData.node1247 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1248
  · rfl
  · exact treeEq1254

theorem accepted1247 : B1247.accepted = true := by decide +kernel
theorem checked1247 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1247 (maskNeeds ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1247]
  exact B1247.sound accepted1247
#print axioms checked1247

def Tip1245_1247 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1247 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1247
def B1266 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq1266 : B1266.tree = HexagonCover.NBand.M7300_7500.SplitData.node1266 := by
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

def B1265 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B1266, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1265 : B1265.tree = HexagonCover.NBand.M7300_7500.SplitData.node1265 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1266
  · rfl
  · rfl

def B1264 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1265]
theorem treeEq1264 : B1264.tree = HexagonCover.NBand.M7300_7500.SplitData.node1264 := by
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
  · exact treeEq1265

def B1263 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B1264, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1263 : B1263.tree = HexagonCover.NBand.M7300_7500.SplitData.node1263 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1264
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1262 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1263]
theorem treeEq1262 : B1262.tree = HexagonCover.NBand.M7300_7500.SplitData.node1262 := by
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
  · exact treeEq1263

def B1261 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B1262, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1261 : B1261.tree = HexagonCover.NBand.M7300_7500.SplitData.node1261 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1262
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1260 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1261, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1260 : B1260.tree = HexagonCover.NBand.M7300_7500.SplitData.node1260 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1261
  · rfl

def B1259 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1260, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1259 : B1259.tree = HexagonCover.NBand.M7300_7500.SplitData.node1259 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1260
  · rfl
  · rfl

def B1246 : Block := .branch 101 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip1245_1247, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B1259]
theorem treeEq1246 : B1246.tree = HexagonCover.NBand.M7300_7500.SplitData.node1246 := by
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
  · exact treeEq1259

def B1274 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq1274 : B1274.tree = HexagonCover.NBand.M7300_7500.SplitData.node1274 := by
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

def B1273 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B1274, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1273 : B1273.tree = HexagonCover.NBand.M7300_7500.SplitData.node1273 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1274
  · rfl
  · rfl

def B1272 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1273]
theorem treeEq1272 : B1272.tree = HexagonCover.NBand.M7300_7500.SplitData.node1272 := by
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
  · exact treeEq1273

def B1271 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B1272, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1271 : B1271.tree = HexagonCover.NBand.M7300_7500.SplitData.node1271 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1272
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1270 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1271]
theorem treeEq1270 : B1270.tree = HexagonCover.NBand.M7300_7500.SplitData.node1270 := by
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
  · exact treeEq1271

def B1269 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B1270, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1269 : B1269.tree = HexagonCover.NBand.M7300_7500.SplitData.node1269 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1270
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1268 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1269, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1268 : B1268.tree = HexagonCover.NBand.M7300_7500.SplitData.node1268 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1269
  · rfl

def B1267 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1268, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1267 : B1267.tree = HexagonCover.NBand.M7300_7500.SplitData.node1267 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1268
  · rfl
  · rfl

def B1245 : Block := .branch 91 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B1246, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B1267]
theorem treeEq1245 : B1245.tree = HexagonCover.NBand.M7300_7500.SplitData.node1245 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1246
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1267

theorem accepted1245 : B1245.accepted = true := by decide +kernel
theorem checked1245 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1245 (maskNeeds ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1245]
  exact B1245.sound accepted1245
#print axioms checked1245

def Tip1243_1245 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1245 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1245
def B1282 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq1282 : B1282.tree = HexagonCover.NBand.M7300_7500.SplitData.node1282 := by
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

def B1281 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1282, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq1281 : B1281.tree = HexagonCover.NBand.M7300_7500.SplitData.node1281 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1282
  · rfl
  · rfl

def B1280 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1281]
theorem treeEq1280 : B1280.tree = HexagonCover.NBand.M7300_7500.SplitData.node1280 := by
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
  · exact treeEq1281

def B1279 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B1280, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1279 : B1279.tree = HexagonCover.NBand.M7300_7500.SplitData.node1279 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1280
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1278 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1279]
theorem treeEq1278 : B1278.tree = HexagonCover.NBand.M7300_7500.SplitData.node1278 := by
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
  · exact treeEq1279

def B1277 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B1278, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1277 : B1277.tree = HexagonCover.NBand.M7300_7500.SplitData.node1277 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1278
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1276 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1277, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1276 : B1276.tree = HexagonCover.NBand.M7300_7500.SplitData.node1276 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1277
  · rfl

def B1275 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1276, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq1275 : B1275.tree = HexagonCover.NBand.M7300_7500.SplitData.node1275 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1276
  · rfl
  · rfl

def B1244 : Block := .branch 89 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip1243_1245, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1275]
theorem treeEq1244 : B1244.tree = HexagonCover.NBand.M7300_7500.SplitData.node1244 := by
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
  · exact treeEq1275

def B1290 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq1290 : B1290.tree = HexagonCover.NBand.M7300_7500.SplitData.node1290 := by
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

def B1289 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1290, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq1289 : B1289.tree = HexagonCover.NBand.M7300_7500.SplitData.node1289 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1290
  · rfl
  · rfl

def B1288 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1289]
theorem treeEq1288 : B1288.tree = HexagonCover.NBand.M7300_7500.SplitData.node1288 := by
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
  · exact treeEq1289

def B1287 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B1288, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1287 : B1287.tree = HexagonCover.NBand.M7300_7500.SplitData.node1287 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1288
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1286 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1287]
theorem treeEq1286 : B1286.tree = HexagonCover.NBand.M7300_7500.SplitData.node1286 := by
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
  · exact treeEq1287

def B1285 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B1286, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1285 : B1285.tree = HexagonCover.NBand.M7300_7500.SplitData.node1285 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1286
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1284 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1285, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1284 : B1284.tree = HexagonCover.NBand.M7300_7500.SplitData.node1284 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1285
  · rfl

def B1283 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1284, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq1283 : B1283.tree = HexagonCover.NBand.M7300_7500.SplitData.node1283 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1284
  · rfl
  · rfl

def B1243 : Block := .branch 86 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B1244, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B1283]
theorem treeEq1243 : B1243.tree = HexagonCover.NBand.M7300_7500.SplitData.node1243 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1244
  · rfl
  · rfl
  · exact treeEq1283

theorem accepted1243 : B1243.accepted = true := by decide +kernel
theorem checked1243 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1243 (maskNeeds ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1243]
  exact B1243.sound accepted1243
#print axioms checked1243

def B1324 : Block := .branch 142 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 24114777037737969633617774127089565776794307002432] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1324 : B1324.tree = HexagonCover.NBand.M7300_7500.SplitData.node1324 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1323 : Block := .branch 159 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B1324]
theorem treeEq1323 : B1323.tree = HexagonCover.NBand.M7300_7500.SplitData.node1323 := by
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
  · exact treeEq1324

def B1322 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1323]
theorem treeEq1322 : B1322.tree = HexagonCover.NBand.M7300_7500.SplitData.node1322 := by
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
  · exact treeEq1323

def B1321 : Block := .branch 169 ![2535301200456458802993406411137, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B1322, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1321 : B1321.tree = HexagonCover.NBand.M7300_7500.SplitData.node1321 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1322
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1320 : Block := .branch 170 ![2535301200456458802993406411137, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 679).pointIds 679), B1321, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1320 : B1320.tree = HexagonCover.NBand.M7300_7500.SplitData.node1320 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1321
  · rfl

def B1329 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1329 : B1329.tree = HexagonCover.NBand.M7300_7500.SplitData.node1329 := by
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
  · rfl

def B1328 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B1329]
theorem treeEq1328 : B1328.tree = HexagonCover.NBand.M7300_7500.SplitData.node1328 := by
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
  · exact treeEq1329

def B1327 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 42535295865117307932921825928971419680, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), B1328, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1327 : B1327.tree = HexagonCover.NBand.M7300_7500.SplitData.node1327 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1328
  · rfl
  · rfl

def B1326 : Block := .branch 125 ![374144419156711157447272335445480168895904795853185, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 393248, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B1327, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1326 : B1326.tree = HexagonCover.NBand.M7300_7500.SplitData.node1326 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1327
  · rfl

def B1325 : Block := .branch 168 ![10387129018270111715863986064851329, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071807775992273212354753230527791168] ![B1326, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1325 : B1325.tree = HexagonCover.NBand.M7300_7500.SplitData.node1325 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1326
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1319 : Block := .branch 108 ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B1320, (.leaf 5 (Common.fact 308).pointIds 308), B1325]
theorem treeEq1319 : B1319.tree = HexagonCover.NBand.M7300_7500.SplitData.node1319 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1320
  · rfl
  · exact treeEq1325

theorem accepted1319 : B1319.accepted = true := by decide +kernel
theorem checked1319 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1319 (maskNeeds ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1319]
  exact B1319.sound accepted1319
#print axioms checked1319

def Tip1317_1319 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1319 ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked1319
def B1338 : Block := .branch 109 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq1338 : B1338.tree = HexagonCover.NBand.M7300_7500.SplitData.node1338 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1337 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B1338, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq1337 : B1337.tree = HexagonCover.NBand.M7300_7500.SplitData.node1337 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1338
  · rfl
  · rfl

def B1336 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B1337, (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq1336 : B1336.tree = HexagonCover.NBand.M7300_7500.SplitData.node1336 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1337
  · rfl

def B1335 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1336]
theorem treeEq1335 : B1335.tree = HexagonCover.NBand.M7300_7500.SplitData.node1335 := by
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
  · exact treeEq1336

def B1334 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![B1335, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1334 : B1334.tree = HexagonCover.NBand.M7300_7500.SplitData.node1334 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1335
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1333 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1334]
theorem treeEq1333 : B1333.tree = HexagonCover.NBand.M7300_7500.SplitData.node1333 := by
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
  · exact treeEq1334

def B1332 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739815242086773067913625664] ![B1333, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1332 : B1332.tree = HexagonCover.NBand.M7300_7500.SplitData.node1332 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1333
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1331 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1332, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1331 : B1331.tree = HexagonCover.NBand.M7300_7500.SplitData.node1331 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1332
  · rfl

def B1330 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1331, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq1330 : B1330.tree = HexagonCover.NBand.M7300_7500.SplitData.node1330 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1331
  · rfl
  · rfl

def B1318 : Block := .branch 101 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip1317_1319, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B1330]
theorem treeEq1318 : B1318.tree = HexagonCover.NBand.M7300_7500.SplitData.node1318 := by
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
  · exact treeEq1330

def B1346 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1346 : B1346.tree = HexagonCover.NBand.M7300_7500.SplitData.node1346 := by
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

def B1345 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1346, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq1345 : B1345.tree = HexagonCover.NBand.M7300_7500.SplitData.node1345 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1346
  · rfl
  · rfl

def B1344 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1345]
theorem treeEq1344 : B1344.tree = HexagonCover.NBand.M7300_7500.SplitData.node1344 := by
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
  · exact treeEq1345

def B1343 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B1344, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1343 : B1343.tree = HexagonCover.NBand.M7300_7500.SplitData.node1343 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1344
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1342 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1343]
theorem treeEq1342 : B1342.tree = HexagonCover.NBand.M7300_7500.SplitData.node1342 := by
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
  · exact treeEq1343

def B1341 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B1342, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1341 : B1341.tree = HexagonCover.NBand.M7300_7500.SplitData.node1341 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1342
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1340 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1341, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1340 : B1340.tree = HexagonCover.NBand.M7300_7500.SplitData.node1340 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1341
  · rfl

def B1339 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1340, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1339 : B1339.tree = HexagonCover.NBand.M7300_7500.SplitData.node1339 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1340
  · rfl
  · rfl

def B1317 : Block := .branch 89 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 86).pointIds 86), B1318, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1339]
theorem treeEq1317 : B1317.tree = HexagonCover.NBand.M7300_7500.SplitData.node1317 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1318
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1339

theorem accepted1317 : B1317.accepted = true := by decide +kernel
theorem checked1317 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1317 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1317]
  exact B1317.sound accepted1317
#print axioms checked1317

end HexagonCover.NBand.M7300_7500.SplitTree.Run0017
