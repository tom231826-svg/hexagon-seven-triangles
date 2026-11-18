import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0044
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0045
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B3233 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3233 : B3233.tree = HexagonCover.NBand.M7300_7500.SplitData.node3233 := by
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

def B3232 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3233]
theorem treeEq3232 : B3232.tree = HexagonCover.NBand.M7300_7500.SplitData.node3232 := by
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
  · exact treeEq3233

def B3231 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3232, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3231 : B3231.tree = HexagonCover.NBand.M7300_7500.SplitData.node3231 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3232
  · rfl
  · rfl

def B3230 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3231, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3230 : B3230.tree = HexagonCover.NBand.M7300_7500.SplitData.node3230 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3231
  · rfl

def B3229 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3230, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3229 : B3229.tree = HexagonCover.NBand.M7300_7500.SplitData.node3229 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3230
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3228 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3229]
theorem treeEq3228 : B3228.tree = HexagonCover.NBand.M7300_7500.SplitData.node3228 := by
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
  · exact treeEq3229

def B3227 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3228, (.leaf 0 [] 0)]
theorem treeEq3227 : B3227.tree = HexagonCover.NBand.M7300_7500.SplitData.node3227 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3228
  · rfl

def B3226 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3227, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3226 : B3226.tree = HexagonCover.NBand.M7300_7500.SplitData.node3226 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3227
  · rfl

def B3225 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3226, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3225 : B3225.tree = HexagonCover.NBand.M7300_7500.SplitData.node3225 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3226
  · rfl
  · rfl

def B3224 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3225]
theorem treeEq3224 : B3224.tree = HexagonCover.NBand.M7300_7500.SplitData.node3224 := by
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
  · exact treeEq3225

def B3241 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3241 : B3241.tree = HexagonCover.NBand.M7300_7500.SplitData.node3241 := by
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

def B3240 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B3241, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3240 : B3240.tree = HexagonCover.NBand.M7300_7500.SplitData.node3240 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3241
  · rfl
  · rfl

def B3239 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3240]
theorem treeEq3239 : B3239.tree = HexagonCover.NBand.M7300_7500.SplitData.node3239 := by
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
  · exact treeEq3240

def B3238 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3239, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3238 : B3238.tree = HexagonCover.NBand.M7300_7500.SplitData.node3238 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3239
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3237 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3238]
theorem treeEq3237 : B3237.tree = HexagonCover.NBand.M7300_7500.SplitData.node3237 := by
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
  · exact treeEq3238

def B3236 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3237, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3236 : B3236.tree = HexagonCover.NBand.M7300_7500.SplitData.node3236 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3237
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3235 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3236, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3235 : B3235.tree = HexagonCover.NBand.M7300_7500.SplitData.node3235 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3236
  · rfl

def B3234 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3235, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3234 : B3234.tree = HexagonCover.NBand.M7300_7500.SplitData.node3234 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3235
  · rfl
  · rfl

def B3223 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3224, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3234]
theorem treeEq3223 : B3223.tree = HexagonCover.NBand.M7300_7500.SplitData.node3223 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3224
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3234

theorem accepted3223 : B3223.accepted = true := by decide +kernel
theorem checked3223 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3223 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3223]
  exact B3223.sound accepted3223
#print axioms checked3223

def B3262 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3262 : B3262.tree = HexagonCover.NBand.M7300_7500.SplitData.node3262 := by
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

def B3261 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3262]
theorem treeEq3261 : B3261.tree = HexagonCover.NBand.M7300_7500.SplitData.node3261 := by
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
  · exact treeEq3262

def B3260 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3261, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3260 : B3260.tree = HexagonCover.NBand.M7300_7500.SplitData.node3260 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3261
  · rfl
  · rfl

def B3259 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3260, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3259 : B3259.tree = HexagonCover.NBand.M7300_7500.SplitData.node3259 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3260
  · rfl

def B3258 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3259, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3258 : B3258.tree = HexagonCover.NBand.M7300_7500.SplitData.node3258 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3259
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3257 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3258]
theorem treeEq3257 : B3257.tree = HexagonCover.NBand.M7300_7500.SplitData.node3257 := by
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
  · exact treeEq3258

def B3256 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3257, (.leaf 0 [] 0)]
theorem treeEq3256 : B3256.tree = HexagonCover.NBand.M7300_7500.SplitData.node3256 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3257
  · rfl

def B3255 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3256, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3255 : B3255.tree = HexagonCover.NBand.M7300_7500.SplitData.node3255 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3256
  · rfl

def B3254 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3255, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3254 : B3254.tree = HexagonCover.NBand.M7300_7500.SplitData.node3254 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3255
  · rfl
  · rfl

def B3253 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3254]
theorem treeEq3253 : B3253.tree = HexagonCover.NBand.M7300_7500.SplitData.node3253 := by
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
  · exact treeEq3254

def B3270 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3270 : B3270.tree = HexagonCover.NBand.M7300_7500.SplitData.node3270 := by
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

def B3269 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B3270, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3269 : B3269.tree = HexagonCover.NBand.M7300_7500.SplitData.node3269 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3270
  · rfl
  · rfl

def B3268 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3269]
theorem treeEq3268 : B3268.tree = HexagonCover.NBand.M7300_7500.SplitData.node3268 := by
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
  · exact treeEq3269

def B3267 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3268, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3267 : B3267.tree = HexagonCover.NBand.M7300_7500.SplitData.node3267 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3268
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3266 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3267]
theorem treeEq3266 : B3266.tree = HexagonCover.NBand.M7300_7500.SplitData.node3266 := by
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
  · exact treeEq3267

def B3265 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3266, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3265 : B3265.tree = HexagonCover.NBand.M7300_7500.SplitData.node3265 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3266
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3264 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3265, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3264 : B3264.tree = HexagonCover.NBand.M7300_7500.SplitData.node3264 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3265
  · rfl

def B3263 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3264, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3263 : B3263.tree = HexagonCover.NBand.M7300_7500.SplitData.node3263 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3264
  · rfl
  · rfl

def B3252 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3253, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3263]
theorem treeEq3252 : B3252.tree = HexagonCover.NBand.M7300_7500.SplitData.node3252 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3253
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3263

theorem accepted3252 : B3252.accepted = true := by decide +kernel
theorem checked3252 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3252 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3252]
  exact B3252.sound accepted3252
#print axioms checked3252

def Tip3222_3223 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3223 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3223
def B3250 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3250 : B3250.tree = HexagonCover.NBand.M7300_7500.SplitData.node3250 := by
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

def B3249 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3250]
theorem treeEq3249 : B3249.tree = HexagonCover.NBand.M7300_7500.SplitData.node3249 := by
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
  · exact treeEq3250

def B3248 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3249, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3248 : B3248.tree = HexagonCover.NBand.M7300_7500.SplitData.node3248 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3249
  · rfl
  · rfl

def B3247 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3248, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3247 : B3247.tree = HexagonCover.NBand.M7300_7500.SplitData.node3247 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3248
  · rfl

def B3246 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3247, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3246 : B3246.tree = HexagonCover.NBand.M7300_7500.SplitData.node3246 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3247
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3245 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3246]
theorem treeEq3245 : B3245.tree = HexagonCover.NBand.M7300_7500.SplitData.node3245 := by
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
  · exact treeEq3246

def B3244 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3245, (.leaf 0 [] 0)]
theorem treeEq3244 : B3244.tree = HexagonCover.NBand.M7300_7500.SplitData.node3244 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3245
  · rfl

def B3243 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3244, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3243 : B3243.tree = HexagonCover.NBand.M7300_7500.SplitData.node3243 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3244
  · rfl

def B3242 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3243, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3242 : B3242.tree = HexagonCover.NBand.M7300_7500.SplitData.node3242 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3243
  · rfl
  · rfl

def B3222 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3222_3223, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3242]
theorem treeEq3222 : B3222.tree = HexagonCover.NBand.M7300_7500.SplitData.node3222 := by
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
  · exact treeEq3242

theorem accepted3222 : B3222.accepted = true := by decide +kernel
theorem checked3222 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3222 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3222]
  exact B3222.sound accepted3222
#print axioms checked3222

def Tip3162_3193 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3193 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0044.checked3193
def Tip3162_3163 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3163 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0044.checked3163
def B3220 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3220 : B3220.tree = HexagonCover.NBand.M7300_7500.SplitData.node3220 := by
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

def B3219 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3220]
theorem treeEq3219 : B3219.tree = HexagonCover.NBand.M7300_7500.SplitData.node3219 := by
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
  · exact treeEq3220

def B3218 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3219, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3218 : B3218.tree = HexagonCover.NBand.M7300_7500.SplitData.node3218 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3219
  · rfl
  · rfl

def B3217 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3218, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3217 : B3217.tree = HexagonCover.NBand.M7300_7500.SplitData.node3217 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3218
  · rfl

def B3216 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3217, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3216 : B3216.tree = HexagonCover.NBand.M7300_7500.SplitData.node3216 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3217
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3215 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3216]
theorem treeEq3215 : B3215.tree = HexagonCover.NBand.M7300_7500.SplitData.node3215 := by
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
  · exact treeEq3216

def B3214 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3215, (.leaf 0 [] 0)]
theorem treeEq3214 : B3214.tree = HexagonCover.NBand.M7300_7500.SplitData.node3214 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3215
  · rfl

def B3213 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3214, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3213 : B3213.tree = HexagonCover.NBand.M7300_7500.SplitData.node3213 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3214
  · rfl

def B3212 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3213, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3212 : B3212.tree = HexagonCover.NBand.M7300_7500.SplitData.node3212 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3213
  · rfl
  · rfl

def B3192 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3162_3193, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3212]
theorem treeEq3192 : B3192.tree = HexagonCover.NBand.M7300_7500.SplitData.node3192 := by
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
  · exact treeEq3212

def B3162 : Block := .branch 74 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip3162_3163, B3192, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3162 : B3162.tree = HexagonCover.NBand.M7300_7500.SplitData.node3162 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3192
  · rfl
  · rfl
  · rfl

theorem accepted3162 : B3162.accepted = true := by decide +kernel
theorem checked3162 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3162 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3162]
  exact B3162.sound accepted3162
#print axioms checked3162

def Tip3161_3252 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3252 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3252
def Tip3161_3222 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3222 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3222
def Tip3161_3162 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3162 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3162
def B3279 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3279 : B3279.tree = HexagonCover.NBand.M7300_7500.SplitData.node3279 := by
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

def B3278 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3279]
theorem treeEq3278 : B3278.tree = HexagonCover.NBand.M7300_7500.SplitData.node3278 := by
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
  · exact treeEq3279

def B3277 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3278, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3277 : B3277.tree = HexagonCover.NBand.M7300_7500.SplitData.node3277 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3278
  · rfl
  · rfl

def B3276 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3277, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3276 : B3276.tree = HexagonCover.NBand.M7300_7500.SplitData.node3276 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3277
  · rfl

def B3275 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3276, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3275 : B3275.tree = HexagonCover.NBand.M7300_7500.SplitData.node3275 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3276
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3274 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3275]
theorem treeEq3274 : B3274.tree = HexagonCover.NBand.M7300_7500.SplitData.node3274 := by
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
  · exact treeEq3275

def B3273 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3274, (.leaf 0 [] 0)]
theorem treeEq3273 : B3273.tree = HexagonCover.NBand.M7300_7500.SplitData.node3273 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3274
  · rfl

def B3272 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3273, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3272 : B3272.tree = HexagonCover.NBand.M7300_7500.SplitData.node3272 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3273
  · rfl

def B3271 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3272, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3271 : B3271.tree = HexagonCover.NBand.M7300_7500.SplitData.node3271 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3272
  · rfl
  · rfl

def B3251 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3161_3252, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3271]
theorem treeEq3251 : B3251.tree = HexagonCover.NBand.M7300_7500.SplitData.node3251 := by
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
  · exact treeEq3271

def B3221 : Block := .branch 74 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip3161_3222, B3251, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3221 : B3221.tree = HexagonCover.NBand.M7300_7500.SplitData.node3221 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3251
  · rfl
  · rfl
  · rfl

def B3161 : Block := .branch 73 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip3161_3162, B3221, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq3161 : B3161.tree = HexagonCover.NBand.M7300_7500.SplitData.node3161 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3221
  · rfl
  · rfl
  · rfl

theorem accepted3161 : B3161.accepted = true := by decide +kernel
theorem checked3161 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3161 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3161]
  exact B3161.sound accepted3161
#print axioms checked3161

end HexagonCover.NBand.M7300_7500.SplitTree.Run0045
