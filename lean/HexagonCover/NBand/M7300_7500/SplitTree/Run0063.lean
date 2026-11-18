import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0063
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B4513 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq4513 : B4513.tree = HexagonCover.NBand.M7300_7500.SplitData.node4513 := by
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

def B4512 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4513]
theorem treeEq4512 : B4512.tree = HexagonCover.NBand.M7300_7500.SplitData.node4512 := by
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
  · exact treeEq4513

def B4511 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4512, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4511 : B4511.tree = HexagonCover.NBand.M7300_7500.SplitData.node4511 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4512
  · rfl
  · rfl

def B4510 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4511, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq4510 : B4510.tree = HexagonCover.NBand.M7300_7500.SplitData.node4510 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4511
  · rfl

def B4509 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B4510, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq4509 : B4509.tree = HexagonCover.NBand.M7300_7500.SplitData.node4509 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4510
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4508 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4509]
theorem treeEq4508 : B4508.tree = HexagonCover.NBand.M7300_7500.SplitData.node4508 := by
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
  · exact treeEq4509

def B4507 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4508, (.leaf 0 [] 0)]
theorem treeEq4507 : B4507.tree = HexagonCover.NBand.M7300_7500.SplitData.node4507 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4508
  · rfl

def B4506 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4507, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4506 : B4506.tree = HexagonCover.NBand.M7300_7500.SplitData.node4506 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4507
  · rfl

def B4505 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4506, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq4505 : B4505.tree = HexagonCover.NBand.M7300_7500.SplitData.node4505 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4506
  · rfl
  · rfl

def B4504 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671076439407461890, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1012).pointIds 1012), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4505]
theorem treeEq4504 : B4504.tree = HexagonCover.NBand.M7300_7500.SplitData.node4504 := by
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
  · exact treeEq4505

def B4521 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq4521 : B4521.tree = HexagonCover.NBand.M7300_7500.SplitData.node4521 := by
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

def B4520 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B4521, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq4520 : B4520.tree = HexagonCover.NBand.M7300_7500.SplitData.node4520 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4521
  · rfl
  · rfl

def B4519 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4520]
theorem treeEq4519 : B4519.tree = HexagonCover.NBand.M7300_7500.SplitData.node4519 := by
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
  · exact treeEq4520

def B4518 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B4519, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4518 : B4518.tree = HexagonCover.NBand.M7300_7500.SplitData.node4518 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4519
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4517 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4518]
theorem treeEq4517 : B4517.tree = HexagonCover.NBand.M7300_7500.SplitData.node4517 := by
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
  · exact treeEq4518

def B4516 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B4517, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq4516 : B4516.tree = HexagonCover.NBand.M7300_7500.SplitData.node4516 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4517
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4515 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4516, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4515 : B4515.tree = HexagonCover.NBand.M7300_7500.SplitData.node4515 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4516
  · rfl

def B4514 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4515, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq4514 : B4514.tree = HexagonCover.NBand.M7300_7500.SplitData.node4514 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4515
  · rfl
  · rfl

def B4503 : Block := .branch 78 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B4504, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B4514]
theorem treeEq4503 : B4503.tree = HexagonCover.NBand.M7300_7500.SplitData.node4503 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4504
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4514

theorem accepted4503 : B4503.accepted = true := by decide +kernel
theorem checked4503 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4503 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4503]
  exact B4503.sound accepted4503
#print axioms checked4503

def B4542 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq4542 : B4542.tree = HexagonCover.NBand.M7300_7500.SplitData.node4542 := by
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

def B4541 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4542]
theorem treeEq4541 : B4541.tree = HexagonCover.NBand.M7300_7500.SplitData.node4541 := by
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
  · exact treeEq4542

def B4540 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4541, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4540 : B4540.tree = HexagonCover.NBand.M7300_7500.SplitData.node4540 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4541
  · rfl
  · rfl

def B4539 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4540, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq4539 : B4539.tree = HexagonCover.NBand.M7300_7500.SplitData.node4539 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4540
  · rfl

def B4538 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B4539, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq4538 : B4538.tree = HexagonCover.NBand.M7300_7500.SplitData.node4538 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4539
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4537 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4538]
theorem treeEq4537 : B4537.tree = HexagonCover.NBand.M7300_7500.SplitData.node4537 := by
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
  · exact treeEq4538

def B4536 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4537, (.leaf 0 [] 0)]
theorem treeEq4536 : B4536.tree = HexagonCover.NBand.M7300_7500.SplitData.node4536 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4537
  · rfl

def B4535 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4536, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4535 : B4535.tree = HexagonCover.NBand.M7300_7500.SplitData.node4535 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4536
  · rfl

def B4534 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4535, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq4534 : B4534.tree = HexagonCover.NBand.M7300_7500.SplitData.node4534 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4535
  · rfl
  · rfl

def B4533 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671076439407461890, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1012).pointIds 1012), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4534]
theorem treeEq4533 : B4533.tree = HexagonCover.NBand.M7300_7500.SplitData.node4533 := by
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
  · exact treeEq4534

def B4550 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq4550 : B4550.tree = HexagonCover.NBand.M7300_7500.SplitData.node4550 := by
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

def B4549 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B4550, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq4549 : B4549.tree = HexagonCover.NBand.M7300_7500.SplitData.node4549 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4550
  · rfl
  · rfl

def B4548 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4549]
theorem treeEq4548 : B4548.tree = HexagonCover.NBand.M7300_7500.SplitData.node4548 := by
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
  · exact treeEq4549

def B4547 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B4548, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4547 : B4547.tree = HexagonCover.NBand.M7300_7500.SplitData.node4547 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4548
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4546 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4547]
theorem treeEq4546 : B4546.tree = HexagonCover.NBand.M7300_7500.SplitData.node4546 := by
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
  · exact treeEq4547

def B4545 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B4546, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq4545 : B4545.tree = HexagonCover.NBand.M7300_7500.SplitData.node4545 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4546
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4544 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4545, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4544 : B4544.tree = HexagonCover.NBand.M7300_7500.SplitData.node4544 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4545
  · rfl

def B4543 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4544, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq4543 : B4543.tree = HexagonCover.NBand.M7300_7500.SplitData.node4543 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4544
  · rfl
  · rfl

def B4532 : Block := .branch 78 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B4533, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B4543]
theorem treeEq4532 : B4532.tree = HexagonCover.NBand.M7300_7500.SplitData.node4532 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4533
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4543

theorem accepted4532 : B4532.accepted = true := by decide +kernel
theorem checked4532 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4532 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4532]
  exact B4532.sound accepted4532
#print axioms checked4532

def Tip4502_4503 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4503 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked4503
def B4530 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq4530 : B4530.tree = HexagonCover.NBand.M7300_7500.SplitData.node4530 := by
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

def B4529 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4530]
theorem treeEq4529 : B4529.tree = HexagonCover.NBand.M7300_7500.SplitData.node4529 := by
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
  · exact treeEq4530

def B4528 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4529, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4528 : B4528.tree = HexagonCover.NBand.M7300_7500.SplitData.node4528 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4529
  · rfl
  · rfl

def B4527 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4528, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq4527 : B4527.tree = HexagonCover.NBand.M7300_7500.SplitData.node4527 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4528
  · rfl

def B4526 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B4527, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq4526 : B4526.tree = HexagonCover.NBand.M7300_7500.SplitData.node4526 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4527
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4525 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4526]
theorem treeEq4525 : B4525.tree = HexagonCover.NBand.M7300_7500.SplitData.node4525 := by
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
  · exact treeEq4526

def B4524 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4525, (.leaf 0 [] 0)]
theorem treeEq4524 : B4524.tree = HexagonCover.NBand.M7300_7500.SplitData.node4524 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4525
  · rfl

def B4523 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4524, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4523 : B4523.tree = HexagonCover.NBand.M7300_7500.SplitData.node4523 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4524
  · rfl

def B4522 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4523, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq4522 : B4522.tree = HexagonCover.NBand.M7300_7500.SplitData.node4522 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4523
  · rfl
  · rfl

def B4502 : Block := .branch 76 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip4502_4503, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B4522]
theorem treeEq4502 : B4502.tree = HexagonCover.NBand.M7300_7500.SplitData.node4502 := by
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
  · exact treeEq4522

theorem accepted4502 : B4502.accepted = true := by decide +kernel
theorem checked4502 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4502 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4502]
  exact B4502.sound accepted4502
#print axioms checked4502

def B4572 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq4572 : B4572.tree = HexagonCover.NBand.M7300_7500.SplitData.node4572 := by
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

def B4571 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4572]
theorem treeEq4571 : B4571.tree = HexagonCover.NBand.M7300_7500.SplitData.node4571 := by
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
  · exact treeEq4572

def B4570 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4571, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4570 : B4570.tree = HexagonCover.NBand.M7300_7500.SplitData.node4570 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4571
  · rfl
  · rfl

def B4569 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4570, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq4569 : B4569.tree = HexagonCover.NBand.M7300_7500.SplitData.node4569 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4570
  · rfl

def B4568 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B4569, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq4568 : B4568.tree = HexagonCover.NBand.M7300_7500.SplitData.node4568 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4569
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4567 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4568]
theorem treeEq4567 : B4567.tree = HexagonCover.NBand.M7300_7500.SplitData.node4567 := by
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
  · exact treeEq4568

def B4566 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4567, (.leaf 0 [] 0)]
theorem treeEq4566 : B4566.tree = HexagonCover.NBand.M7300_7500.SplitData.node4566 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4567
  · rfl

def B4565 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4566, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4565 : B4565.tree = HexagonCover.NBand.M7300_7500.SplitData.node4565 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4566
  · rfl

def B4564 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4565, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq4564 : B4564.tree = HexagonCover.NBand.M7300_7500.SplitData.node4564 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4565
  · rfl
  · rfl

def B4563 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671076439407461890, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1012).pointIds 1012), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4564]
theorem treeEq4563 : B4563.tree = HexagonCover.NBand.M7300_7500.SplitData.node4563 := by
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
  · exact treeEq4564

def B4580 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq4580 : B4580.tree = HexagonCover.NBand.M7300_7500.SplitData.node4580 := by
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

def B4579 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B4580, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq4579 : B4579.tree = HexagonCover.NBand.M7300_7500.SplitData.node4579 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4580
  · rfl
  · rfl

def B4578 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4579]
theorem treeEq4578 : B4578.tree = HexagonCover.NBand.M7300_7500.SplitData.node4578 := by
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
  · exact treeEq4579

def B4577 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B4578, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4577 : B4577.tree = HexagonCover.NBand.M7300_7500.SplitData.node4577 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4578
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4576 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4577]
theorem treeEq4576 : B4576.tree = HexagonCover.NBand.M7300_7500.SplitData.node4576 := by
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
  · exact treeEq4577

def B4575 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B4576, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq4575 : B4575.tree = HexagonCover.NBand.M7300_7500.SplitData.node4575 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4576
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4574 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4575, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4574 : B4574.tree = HexagonCover.NBand.M7300_7500.SplitData.node4574 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4575
  · rfl

def B4573 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4574, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq4573 : B4573.tree = HexagonCover.NBand.M7300_7500.SplitData.node4573 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4574
  · rfl
  · rfl

def B4562 : Block := .branch 78 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B4563, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B4573]
theorem treeEq4562 : B4562.tree = HexagonCover.NBand.M7300_7500.SplitData.node4562 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4563
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4573

theorem accepted4562 : B4562.accepted = true := by decide +kernel
theorem checked4562 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4562 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4562]
  exact B4562.sound accepted4562
#print axioms checked4562

end HexagonCover.NBand.M7300_7500.SplitTree.Run0063
