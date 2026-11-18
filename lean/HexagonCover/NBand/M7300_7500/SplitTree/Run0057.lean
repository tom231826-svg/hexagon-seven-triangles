import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0057
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B4114 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq4114 : B4114.tree = HexagonCover.NBand.M7300_7500.SplitData.node4114 := by
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

def B4113 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4114]
theorem treeEq4113 : B4113.tree = HexagonCover.NBand.M7300_7500.SplitData.node4113 := by
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
  · exact treeEq4114

def B4112 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4113, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4112 : B4112.tree = HexagonCover.NBand.M7300_7500.SplitData.node4112 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4113
  · rfl
  · rfl

def B4111 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4112, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq4111 : B4111.tree = HexagonCover.NBand.M7300_7500.SplitData.node4111 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4112
  · rfl

def B4110 : Block := .branch 168 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B4111, (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq4110 : B4110.tree = HexagonCover.NBand.M7300_7500.SplitData.node4110 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4111
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4109 : Block := .branch 163 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4110]
theorem treeEq4109 : B4109.tree = HexagonCover.NBand.M7300_7500.SplitData.node4109 := by
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
  · exact treeEq4110

def B4108 : Block := .branch 165 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4109, (.leaf 0 [] 0)]
theorem treeEq4108 : B4108.tree = HexagonCover.NBand.M7300_7500.SplitData.node4108 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4109
  · rfl

def B4107 : Block := .branch 167 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4108, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4107 : B4107.tree = HexagonCover.NBand.M7300_7500.SplitData.node4107 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4108
  · rfl

def B4106 : Block := .branch 142 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4107, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq4106 : B4106.tree = HexagonCover.NBand.M7300_7500.SplitData.node4106 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4107
  · rfl
  · rfl

def B4105 : Block := .branch 88 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4106]
theorem treeEq4105 : B4105.tree = HexagonCover.NBand.M7300_7500.SplitData.node4105 := by
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
  · exact treeEq4106

def B4122 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq4122 : B4122.tree = HexagonCover.NBand.M7300_7500.SplitData.node4122 := by
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

def B4121 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B4122, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq4121 : B4121.tree = HexagonCover.NBand.M7300_7500.SplitData.node4121 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4122
  · rfl
  · rfl

def B4120 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B4121, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq4120 : B4120.tree = HexagonCover.NBand.M7300_7500.SplitData.node4120 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4121
  · rfl

def B4119 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B4120, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4119 : B4119.tree = HexagonCover.NBand.M7300_7500.SplitData.node4119 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4120
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4118 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4119]
theorem treeEq4118 : B4118.tree = HexagonCover.NBand.M7300_7500.SplitData.node4118 := by
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
  · exact treeEq4119

def B4117 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B4118, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq4117 : B4117.tree = HexagonCover.NBand.M7300_7500.SplitData.node4117 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4118
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4116 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4117, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4116 : B4116.tree = HexagonCover.NBand.M7300_7500.SplitData.node4116 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4117
  · rfl

def B4115 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4116, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq4115 : B4115.tree = HexagonCover.NBand.M7300_7500.SplitData.node4115 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4116
  · rfl
  · rfl

def B4104 : Block := .branch 78 ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B4105, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B4115]
theorem treeEq4104 : B4104.tree = HexagonCover.NBand.M7300_7500.SplitData.node4104 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4105
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4115

theorem accepted4104 : B4104.accepted = true := by decide +kernel
theorem checked4104 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4104 (maskNeeds ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4104]
  exact B4104.sound accepted4104
#print axioms checked4104

def B4145 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq4145 : B4145.tree = HexagonCover.NBand.M7300_7500.SplitData.node4145 := by
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

def B4144 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4145]
theorem treeEq4144 : B4144.tree = HexagonCover.NBand.M7300_7500.SplitData.node4144 := by
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
  · exact treeEq4145

def B4143 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4144, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4143 : B4143.tree = HexagonCover.NBand.M7300_7500.SplitData.node4143 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4144
  · rfl
  · rfl

def B4142 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4143, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq4142 : B4142.tree = HexagonCover.NBand.M7300_7500.SplitData.node4142 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4143
  · rfl

def B4141 : Block := .branch 168 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B4142, (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq4141 : B4141.tree = HexagonCover.NBand.M7300_7500.SplitData.node4141 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4142
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4140 : Block := .branch 163 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4141]
theorem treeEq4140 : B4140.tree = HexagonCover.NBand.M7300_7500.SplitData.node4140 := by
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
  · exact treeEq4141

def B4139 : Block := .branch 165 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4140, (.leaf 0 [] 0)]
theorem treeEq4139 : B4139.tree = HexagonCover.NBand.M7300_7500.SplitData.node4139 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4140
  · rfl

def B4138 : Block := .branch 167 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4139, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4138 : B4138.tree = HexagonCover.NBand.M7300_7500.SplitData.node4138 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4139
  · rfl

def B4137 : Block := .branch 142 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4138, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq4137 : B4137.tree = HexagonCover.NBand.M7300_7500.SplitData.node4137 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4138
  · rfl
  · rfl

def B4136 : Block := .branch 88 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4137]
theorem treeEq4136 : B4136.tree = HexagonCover.NBand.M7300_7500.SplitData.node4136 := by
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
  · exact treeEq4137

def B4153 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq4153 : B4153.tree = HexagonCover.NBand.M7300_7500.SplitData.node4153 := by
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

def B4152 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B4153, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq4152 : B4152.tree = HexagonCover.NBand.M7300_7500.SplitData.node4152 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4153
  · rfl
  · rfl

def B4151 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B4152, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq4151 : B4151.tree = HexagonCover.NBand.M7300_7500.SplitData.node4151 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4152
  · rfl

def B4150 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B4151, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4150 : B4150.tree = HexagonCover.NBand.M7300_7500.SplitData.node4150 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4151
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4149 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4150]
theorem treeEq4149 : B4149.tree = HexagonCover.NBand.M7300_7500.SplitData.node4149 := by
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
  · exact treeEq4150

def B4148 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B4149, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq4148 : B4148.tree = HexagonCover.NBand.M7300_7500.SplitData.node4148 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4147 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4148, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4147 : B4147.tree = HexagonCover.NBand.M7300_7500.SplitData.node4147 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4148
  · rfl

def B4146 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4147, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq4146 : B4146.tree = HexagonCover.NBand.M7300_7500.SplitData.node4146 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4147
  · rfl
  · rfl

def B4135 : Block := .branch 78 ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B4136, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B4146]
theorem treeEq4135 : B4135.tree = HexagonCover.NBand.M7300_7500.SplitData.node4135 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4136
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4146

theorem accepted4135 : B4135.accepted = true := by decide +kernel
theorem checked4135 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4135 (maskNeeds ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4135]
  exact B4135.sound accepted4135
#print axioms checked4135

def Tip4103_4104 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4104 ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked4104
def B4133 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq4133 : B4133.tree = HexagonCover.NBand.M7300_7500.SplitData.node4133 := by
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

def B4132 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4133]
theorem treeEq4132 : B4132.tree = HexagonCover.NBand.M7300_7500.SplitData.node4132 := by
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
  · exact treeEq4133

def B4131 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4132, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4131 : B4131.tree = HexagonCover.NBand.M7300_7500.SplitData.node4131 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4132
  · rfl
  · rfl

def B4130 : Block := .branch 125 ![374144419156711152252440175710196081562415060222337, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4131, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq4130 : B4130.tree = HexagonCover.NBand.M7300_7500.SplitData.node4130 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4131
  · rfl

def B4129 : Block := .branch 168 ![5192296858534827628530496329220481, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B4130, (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq4129 : B4129.tree = HexagonCover.NBand.M7300_7500.SplitData.node4129 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4130
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4128 : Block := .branch 78 ![5192296858534827628530496329220481, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B4129, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq4128 : B4128.tree = HexagonCover.NBand.M7300_7500.SplitData.node4128 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4129
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4127 : Block := .branch 112 ![385, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B4128, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq4127 : B4127.tree = HexagonCover.NBand.M7300_7500.SplitData.node4127 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4126 : Block := .branch 163 ![385, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4127]
theorem treeEq4126 : B4126.tree = HexagonCover.NBand.M7300_7500.SplitData.node4126 := by
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
  · exact treeEq4127

def B4125 : Block := .branch 165 ![385, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4126, (.leaf 0 [] 0)]
theorem treeEq4125 : B4125.tree = HexagonCover.NBand.M7300_7500.SplitData.node4125 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4126
  · rfl

def B4124 : Block := .branch 167 ![385, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4125, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4124 : B4124.tree = HexagonCover.NBand.M7300_7500.SplitData.node4124 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4125
  · rfl

def B4123 : Block := .branch 142 ![385, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4124, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq4123 : B4123.tree = HexagonCover.NBand.M7300_7500.SplitData.node4123 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4124
  · rfl
  · rfl

def B4103 : Block := .branch 76 ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip4103_4104, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B4123]
theorem treeEq4103 : B4103.tree = HexagonCover.NBand.M7300_7500.SplitData.node4103 := by
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
  · exact treeEq4123

theorem accepted4103 : B4103.accepted = true := by decide +kernel
theorem checked4103 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4103 (maskNeeds ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4103]
  exact B4103.sound accepted4103
#print axioms checked4103

def B4177 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq4177 : B4177.tree = HexagonCover.NBand.M7300_7500.SplitData.node4177 := by
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

def B4176 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4177]
theorem treeEq4176 : B4176.tree = HexagonCover.NBand.M7300_7500.SplitData.node4176 := by
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
  · exact treeEq4177

def B4175 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4176, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4175 : B4175.tree = HexagonCover.NBand.M7300_7500.SplitData.node4175 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4176
  · rfl
  · rfl

def B4174 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4175, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq4174 : B4174.tree = HexagonCover.NBand.M7300_7500.SplitData.node4174 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4175
  · rfl

def B4173 : Block := .branch 168 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B4174, (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq4173 : B4173.tree = HexagonCover.NBand.M7300_7500.SplitData.node4173 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4174
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4172 : Block := .branch 163 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4173]
theorem treeEq4172 : B4172.tree = HexagonCover.NBand.M7300_7500.SplitData.node4172 := by
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
  · exact treeEq4173

def B4171 : Block := .branch 165 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4172, (.leaf 0 [] 0)]
theorem treeEq4171 : B4171.tree = HexagonCover.NBand.M7300_7500.SplitData.node4171 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4172
  · rfl

def B4170 : Block := .branch 167 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4171, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4170 : B4170.tree = HexagonCover.NBand.M7300_7500.SplitData.node4170 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4171
  · rfl

def B4169 : Block := .branch 142 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4170, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq4169 : B4169.tree = HexagonCover.NBand.M7300_7500.SplitData.node4169 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4170
  · rfl
  · rfl

def B4168 : Block := .branch 88 ![10384593717069655257060992658440577, 302231599159582857889282, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4169]
theorem treeEq4168 : B4168.tree = HexagonCover.NBand.M7300_7500.SplitData.node4168 := by
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
  · exact treeEq4169

def B4185 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq4185 : B4185.tree = HexagonCover.NBand.M7300_7500.SplitData.node4185 := by
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

def B4184 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B4185, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq4184 : B4184.tree = HexagonCover.NBand.M7300_7500.SplitData.node4184 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4185
  · rfl
  · rfl

def B4183 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B4184, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq4183 : B4183.tree = HexagonCover.NBand.M7300_7500.SplitData.node4183 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4184
  · rfl

def B4182 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B4183, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4182 : B4182.tree = HexagonCover.NBand.M7300_7500.SplitData.node4182 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4183
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4181 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4182]
theorem treeEq4181 : B4181.tree = HexagonCover.NBand.M7300_7500.SplitData.node4181 := by
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
  · exact treeEq4182

def B4180 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169579491167870274606989376] ![B4181, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq4180 : B4180.tree = HexagonCover.NBand.M7300_7500.SplitData.node4180 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4181
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4179 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4180, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4179 : B4179.tree = HexagonCover.NBand.M7300_7500.SplitData.node4179 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4180
  · rfl

def B4178 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4179, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq4178 : B4178.tree = HexagonCover.NBand.M7300_7500.SplitData.node4178 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4179
  · rfl
  · rfl

def B4167 : Block := .branch 78 ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B4168, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B4178]
theorem treeEq4167 : B4167.tree = HexagonCover.NBand.M7300_7500.SplitData.node4167 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4168
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4178

theorem accepted4167 : B4167.accepted = true := by decide +kernel
theorem checked4167 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4167 (maskNeeds ![10384596192949733827821542456689025, 144255925564212738, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4167]
  exact B4167.sound accepted4167
#print axioms checked4167

end HexagonCover.NBand.M7300_7500.SplitTree.Run0057
