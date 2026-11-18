import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0046
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0047
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B3370 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3370 : B3370.tree = HexagonCover.NBand.M7300_7500.SplitData.node3370 := by
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

def B3369 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3370]
theorem treeEq3369 : B3369.tree = HexagonCover.NBand.M7300_7500.SplitData.node3369 := by
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
  · exact treeEq3370

def B3368 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3369, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3368 : B3368.tree = HexagonCover.NBand.M7300_7500.SplitData.node3368 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3369
  · rfl
  · rfl

def B3367 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3368, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3367 : B3367.tree = HexagonCover.NBand.M7300_7500.SplitData.node3367 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3368
  · rfl

def B3366 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3367, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3366 : B3366.tree = HexagonCover.NBand.M7300_7500.SplitData.node3366 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3367
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3365 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3366]
theorem treeEq3365 : B3365.tree = HexagonCover.NBand.M7300_7500.SplitData.node3365 := by
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
  · exact treeEq3366

def B3364 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3365, (.leaf 0 [] 0)]
theorem treeEq3364 : B3364.tree = HexagonCover.NBand.M7300_7500.SplitData.node3364 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3365
  · rfl

def B3363 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3364, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3363 : B3363.tree = HexagonCover.NBand.M7300_7500.SplitData.node3363 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3364
  · rfl

def B3362 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3363, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3362 : B3362.tree = HexagonCover.NBand.M7300_7500.SplitData.node3362 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3363
  · rfl
  · rfl

def B3361 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3362]
theorem treeEq3361 : B3361.tree = HexagonCover.NBand.M7300_7500.SplitData.node3361 := by
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
  · exact treeEq3362

def B3378 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3378 : B3378.tree = HexagonCover.NBand.M7300_7500.SplitData.node3378 := by
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

def B3377 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), B3378, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3377 : B3377.tree = HexagonCover.NBand.M7300_7500.SplitData.node3377 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3378
  · rfl
  · rfl

def B3376 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3377]
theorem treeEq3376 : B3376.tree = HexagonCover.NBand.M7300_7500.SplitData.node3376 := by
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
  · exact treeEq3377

def B3375 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3376, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3375 : B3375.tree = HexagonCover.NBand.M7300_7500.SplitData.node3375 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3376
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3374 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3375]
theorem treeEq3374 : B3374.tree = HexagonCover.NBand.M7300_7500.SplitData.node3374 := by
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
  · exact treeEq3375

def B3373 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3374, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3373 : B3373.tree = HexagonCover.NBand.M7300_7500.SplitData.node3373 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3374
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3372 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3373, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3372 : B3372.tree = HexagonCover.NBand.M7300_7500.SplitData.node3372 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3373
  · rfl

def B3371 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3372, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3371 : B3371.tree = HexagonCover.NBand.M7300_7500.SplitData.node3371 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3372
  · rfl
  · rfl

def B3360 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3361, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3371]
theorem treeEq3360 : B3360.tree = HexagonCover.NBand.M7300_7500.SplitData.node3360 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3361
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3371

theorem accepted3360 : B3360.accepted = true := by decide +kernel
theorem checked3360 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3360 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3360]
  exact B3360.sound accepted3360
#print axioms checked3360

def B3399 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3399 : B3399.tree = HexagonCover.NBand.M7300_7500.SplitData.node3399 := by
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

def B3398 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3399]
theorem treeEq3398 : B3398.tree = HexagonCover.NBand.M7300_7500.SplitData.node3398 := by
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
  · exact treeEq3399

def B3397 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3398, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3397 : B3397.tree = HexagonCover.NBand.M7300_7500.SplitData.node3397 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3398
  · rfl
  · rfl

def B3396 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3397, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3396 : B3396.tree = HexagonCover.NBand.M7300_7500.SplitData.node3396 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3397
  · rfl

def B3395 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3396, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3395 : B3395.tree = HexagonCover.NBand.M7300_7500.SplitData.node3395 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3396
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3394 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3395]
theorem treeEq3394 : B3394.tree = HexagonCover.NBand.M7300_7500.SplitData.node3394 := by
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
  · exact treeEq3395

def B3393 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3394, (.leaf 0 [] 0)]
theorem treeEq3393 : B3393.tree = HexagonCover.NBand.M7300_7500.SplitData.node3393 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3394
  · rfl

def B3392 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3393, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3392 : B3392.tree = HexagonCover.NBand.M7300_7500.SplitData.node3392 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3393
  · rfl

def B3391 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3392, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3391 : B3391.tree = HexagonCover.NBand.M7300_7500.SplitData.node3391 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3392
  · rfl
  · rfl

def B3390 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3391]
theorem treeEq3390 : B3390.tree = HexagonCover.NBand.M7300_7500.SplitData.node3390 := by
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
  · exact treeEq3391

def B3407 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3407 : B3407.tree = HexagonCover.NBand.M7300_7500.SplitData.node3407 := by
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

def B3406 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), B3407, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3406 : B3406.tree = HexagonCover.NBand.M7300_7500.SplitData.node3406 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3407
  · rfl
  · rfl

def B3405 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3406]
theorem treeEq3405 : B3405.tree = HexagonCover.NBand.M7300_7500.SplitData.node3405 := by
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
  · exact treeEq3406

def B3404 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3405, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3404 : B3404.tree = HexagonCover.NBand.M7300_7500.SplitData.node3404 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3405
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3403 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3404]
theorem treeEq3403 : B3403.tree = HexagonCover.NBand.M7300_7500.SplitData.node3403 := by
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
  · exact treeEq3404

def B3402 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3403, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3402 : B3402.tree = HexagonCover.NBand.M7300_7500.SplitData.node3402 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3403
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3401 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3402, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3401 : B3401.tree = HexagonCover.NBand.M7300_7500.SplitData.node3401 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3402
  · rfl

def B3400 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3401, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3400 : B3400.tree = HexagonCover.NBand.M7300_7500.SplitData.node3400 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3401
  · rfl
  · rfl

def B3389 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3390, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3400]
theorem treeEq3389 : B3389.tree = HexagonCover.NBand.M7300_7500.SplitData.node3389 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3390
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3400

theorem accepted3389 : B3389.accepted = true := by decide +kernel
theorem checked3389 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3389 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3389]
  exact B3389.sound accepted3389
#print axioms checked3389

def Tip3359_3360 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3360 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3360
def B3387 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3387 : B3387.tree = HexagonCover.NBand.M7300_7500.SplitData.node3387 := by
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

def B3386 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3387]
theorem treeEq3386 : B3386.tree = HexagonCover.NBand.M7300_7500.SplitData.node3386 := by
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
  · exact treeEq3387

def B3385 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3386, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3385 : B3385.tree = HexagonCover.NBand.M7300_7500.SplitData.node3385 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3386
  · rfl
  · rfl

def B3384 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3385, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3384 : B3384.tree = HexagonCover.NBand.M7300_7500.SplitData.node3384 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3385
  · rfl

def B3383 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3384, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3383 : B3383.tree = HexagonCover.NBand.M7300_7500.SplitData.node3383 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3384
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3382 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3383]
theorem treeEq3382 : B3382.tree = HexagonCover.NBand.M7300_7500.SplitData.node3382 := by
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
  · exact treeEq3383

def B3381 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3382, (.leaf 0 [] 0)]
theorem treeEq3381 : B3381.tree = HexagonCover.NBand.M7300_7500.SplitData.node3381 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3382
  · rfl

def B3380 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3381, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3380 : B3380.tree = HexagonCover.NBand.M7300_7500.SplitData.node3380 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3381
  · rfl

def B3379 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3380, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3379 : B3379.tree = HexagonCover.NBand.M7300_7500.SplitData.node3379 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3380
  · rfl
  · rfl

def B3359 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3359_3360, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3379]
theorem treeEq3359 : B3359.tree = HexagonCover.NBand.M7300_7500.SplitData.node3359 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3379

theorem accepted3359 : B3359.accepted = true := by decide +kernel
theorem checked3359 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3359 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3359]
  exact B3359.sound accepted3359
#print axioms checked3359

def Tip3299_3330 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3330 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0046.checked3330
def Tip3299_3300 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3300 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0046.checked3300
def B3357 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3357 : B3357.tree = HexagonCover.NBand.M7300_7500.SplitData.node3357 := by
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

def B3356 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3357]
theorem treeEq3356 : B3356.tree = HexagonCover.NBand.M7300_7500.SplitData.node3356 := by
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
  · exact treeEq3357

def B3355 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3356, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3355 : B3355.tree = HexagonCover.NBand.M7300_7500.SplitData.node3355 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3356
  · rfl
  · rfl

def B3354 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3355, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3354 : B3354.tree = HexagonCover.NBand.M7300_7500.SplitData.node3354 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3355
  · rfl

def B3353 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3354, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3353 : B3353.tree = HexagonCover.NBand.M7300_7500.SplitData.node3353 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3354
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3352 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3353]
theorem treeEq3352 : B3352.tree = HexagonCover.NBand.M7300_7500.SplitData.node3352 := by
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
  · exact treeEq3353

def B3351 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3352, (.leaf 0 [] 0)]
theorem treeEq3351 : B3351.tree = HexagonCover.NBand.M7300_7500.SplitData.node3351 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3352
  · rfl

def B3350 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3351, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3350 : B3350.tree = HexagonCover.NBand.M7300_7500.SplitData.node3350 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3351
  · rfl

def B3349 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3350, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3349 : B3349.tree = HexagonCover.NBand.M7300_7500.SplitData.node3349 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3350
  · rfl
  · rfl

def B3329 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3299_3330, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3349]
theorem treeEq3329 : B3329.tree = HexagonCover.NBand.M7300_7500.SplitData.node3329 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3349

def B3299 : Block := .branch 74 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip3299_3300, B3329, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3299 : B3299.tree = HexagonCover.NBand.M7300_7500.SplitData.node3299 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3329
  · rfl
  · rfl
  · rfl

theorem accepted3299 : B3299.accepted = true := by decide +kernel
theorem checked3299 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3299 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3299]
  exact B3299.sound accepted3299
#print axioms checked3299

def B3430 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3430 : B3430.tree = HexagonCover.NBand.M7300_7500.SplitData.node3430 := by
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

def B3429 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3430]
theorem treeEq3429 : B3429.tree = HexagonCover.NBand.M7300_7500.SplitData.node3429 := by
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
  · exact treeEq3430

def B3428 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3429, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3428 : B3428.tree = HexagonCover.NBand.M7300_7500.SplitData.node3428 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3429
  · rfl
  · rfl

def B3427 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3428, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3427 : B3427.tree = HexagonCover.NBand.M7300_7500.SplitData.node3427 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3428
  · rfl

def B3426 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3427, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3426 : B3426.tree = HexagonCover.NBand.M7300_7500.SplitData.node3426 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3427
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3425 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3426]
theorem treeEq3425 : B3425.tree = HexagonCover.NBand.M7300_7500.SplitData.node3425 := by
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
  · exact treeEq3426

def B3424 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3425, (.leaf 0 [] 0)]
theorem treeEq3424 : B3424.tree = HexagonCover.NBand.M7300_7500.SplitData.node3424 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3425
  · rfl

def B3423 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3424, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3423 : B3423.tree = HexagonCover.NBand.M7300_7500.SplitData.node3423 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3424
  · rfl

def B3422 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3423, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3422 : B3422.tree = HexagonCover.NBand.M7300_7500.SplitData.node3422 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3423
  · rfl
  · rfl

def B3421 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3422]
theorem treeEq3421 : B3421.tree = HexagonCover.NBand.M7300_7500.SplitData.node3421 := by
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
  · exact treeEq3422

def B3438 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3438 : B3438.tree = HexagonCover.NBand.M7300_7500.SplitData.node3438 := by
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

def B3437 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), B3438, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3437 : B3437.tree = HexagonCover.NBand.M7300_7500.SplitData.node3437 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3438
  · rfl
  · rfl

def B3436 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3437]
theorem treeEq3436 : B3436.tree = HexagonCover.NBand.M7300_7500.SplitData.node3436 := by
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
  · exact treeEq3437

def B3435 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3436, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3435 : B3435.tree = HexagonCover.NBand.M7300_7500.SplitData.node3435 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3436
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3434 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3435]
theorem treeEq3434 : B3434.tree = HexagonCover.NBand.M7300_7500.SplitData.node3434 := by
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
  · exact treeEq3435

def B3433 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3434, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3433 : B3433.tree = HexagonCover.NBand.M7300_7500.SplitData.node3433 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3434
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3432 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3433, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3432 : B3432.tree = HexagonCover.NBand.M7300_7500.SplitData.node3432 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3433
  · rfl

def B3431 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3432, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3431 : B3431.tree = HexagonCover.NBand.M7300_7500.SplitData.node3431 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3432
  · rfl
  · rfl

def B3420 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3421, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3431]
theorem treeEq3420 : B3420.tree = HexagonCover.NBand.M7300_7500.SplitData.node3420 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3421
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3431

theorem accepted3420 : B3420.accepted = true := by decide +kernel
theorem checked3420 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3420 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3420]
  exact B3420.sound accepted3420
#print axioms checked3420

end HexagonCover.NBand.M7300_7500.SplitTree.Run0047
