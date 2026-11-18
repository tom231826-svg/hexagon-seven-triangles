import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0042
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0043
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip3038_3040 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3040 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0042.checked3040
def B3067 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3067 : B3067.tree = HexagonCover.NBand.M7300_7500.SplitData.node3067 := by
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

def B3066 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3067]
theorem treeEq3066 : B3066.tree = HexagonCover.NBand.M7300_7500.SplitData.node3066 := by
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
  · exact treeEq3067

def B3065 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3066, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3065 : B3065.tree = HexagonCover.NBand.M7300_7500.SplitData.node3065 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3066
  · rfl
  · rfl

def B3064 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3065, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3064 : B3064.tree = HexagonCover.NBand.M7300_7500.SplitData.node3064 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3065
  · rfl

def B3063 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3064, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3063 : B3063.tree = HexagonCover.NBand.M7300_7500.SplitData.node3063 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3064
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3062 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3063]
theorem treeEq3062 : B3062.tree = HexagonCover.NBand.M7300_7500.SplitData.node3062 := by
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
  · exact treeEq3063

def B3061 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3062, (.leaf 0 [] 0)]
theorem treeEq3061 : B3061.tree = HexagonCover.NBand.M7300_7500.SplitData.node3061 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3062
  · rfl

def B3060 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3061, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3060 : B3060.tree = HexagonCover.NBand.M7300_7500.SplitData.node3060 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3061
  · rfl

def B3059 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3060, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3059 : B3059.tree = HexagonCover.NBand.M7300_7500.SplitData.node3059 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3060
  · rfl
  · rfl

def B3039 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3038_3040, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3059]
theorem treeEq3039 : B3039.tree = HexagonCover.NBand.M7300_7500.SplitData.node3039 := by
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
  · exact treeEq3059

def B3076 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq3076 : B3076.tree = HexagonCover.NBand.M7300_7500.SplitData.node3076 := by
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

def B3075 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 98320, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), B3076, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq3075 : B3075.tree = HexagonCover.NBand.M7300_7500.SplitData.node3075 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3076
  · rfl
  · rfl

def B3074 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 393248, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3075]
theorem treeEq3074 : B3074.tree = HexagonCover.NBand.M7300_7500.SplitData.node3074 := by
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
  · exact treeEq3075

def B3073 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![B3074, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq3073 : B3073.tree = HexagonCover.NBand.M7300_7500.SplitData.node3073 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3074
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3072 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 723).pointIds 723), B3073, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3072 : B3072.tree = HexagonCover.NBand.M7300_7500.SplitData.node3072 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3073
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3071 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3072]
theorem treeEq3071 : B3071.tree = HexagonCover.NBand.M7300_7500.SplitData.node3071 := by
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
  · exact treeEq3072

def B3070 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![B3071, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq3070 : B3070.tree = HexagonCover.NBand.M7300_7500.SplitData.node3070 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3071
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3069 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3070, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3069 : B3069.tree = HexagonCover.NBand.M7300_7500.SplitData.node3069 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3070
  · rfl

def B3068 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3069, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq3068 : B3068.tree = HexagonCover.NBand.M7300_7500.SplitData.node3068 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3069
  · rfl
  · rfl

def B3038 : Block := .branch 68 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), B3039, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B3068]
theorem treeEq3038 : B3038.tree = HexagonCover.NBand.M7300_7500.SplitData.node3038 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3039
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3068

theorem accepted3038 : B3038.accepted = true := by decide +kernel
theorem checked3038 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3038 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3038]
  exact B3038.sound accepted3038
#print axioms checked3038

def B3097 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3097 : B3097.tree = HexagonCover.NBand.M7300_7500.SplitData.node3097 := by
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

def B3096 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3097]
theorem treeEq3096 : B3096.tree = HexagonCover.NBand.M7300_7500.SplitData.node3096 := by
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
  · exact treeEq3097

def B3095 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3096, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3095 : B3095.tree = HexagonCover.NBand.M7300_7500.SplitData.node3095 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3096
  · rfl
  · rfl

def B3094 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3095, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3094 : B3094.tree = HexagonCover.NBand.M7300_7500.SplitData.node3094 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3095
  · rfl

def B3093 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3094, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3093 : B3093.tree = HexagonCover.NBand.M7300_7500.SplitData.node3093 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3094
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3092 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3093]
theorem treeEq3092 : B3092.tree = HexagonCover.NBand.M7300_7500.SplitData.node3092 := by
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
  · exact treeEq3093

def B3091 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3092, (.leaf 0 [] 0)]
theorem treeEq3091 : B3091.tree = HexagonCover.NBand.M7300_7500.SplitData.node3091 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3092
  · rfl

def B3090 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3091, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3090 : B3090.tree = HexagonCover.NBand.M7300_7500.SplitData.node3090 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3091
  · rfl

def B3089 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3090, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3089 : B3089.tree = HexagonCover.NBand.M7300_7500.SplitData.node3089 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3090
  · rfl
  · rfl

def B3088 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3089]
theorem treeEq3088 : B3088.tree = HexagonCover.NBand.M7300_7500.SplitData.node3088 := by
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
  · exact treeEq3089

def B3105 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3105 : B3105.tree = HexagonCover.NBand.M7300_7500.SplitData.node3105 := by
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

def B3104 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), B3105, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3104 : B3104.tree = HexagonCover.NBand.M7300_7500.SplitData.node3104 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3105
  · rfl
  · rfl

def B3103 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3104]
theorem treeEq3103 : B3103.tree = HexagonCover.NBand.M7300_7500.SplitData.node3103 := by
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
  · exact treeEq3104

def B3102 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3103, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3102 : B3102.tree = HexagonCover.NBand.M7300_7500.SplitData.node3102 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3103
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3101 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3102]
theorem treeEq3101 : B3101.tree = HexagonCover.NBand.M7300_7500.SplitData.node3101 := by
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
  · exact treeEq3102

def B3100 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3101, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3100 : B3100.tree = HexagonCover.NBand.M7300_7500.SplitData.node3100 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3101
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3099 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3100, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3099 : B3099.tree = HexagonCover.NBand.M7300_7500.SplitData.node3099 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3100
  · rfl

def B3098 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3099, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3098 : B3098.tree = HexagonCover.NBand.M7300_7500.SplitData.node3098 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3099
  · rfl
  · rfl

def B3087 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3088, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3098]
theorem treeEq3087 : B3087.tree = HexagonCover.NBand.M7300_7500.SplitData.node3087 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3088
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3098

theorem accepted3087 : B3087.accepted = true := by decide +kernel
theorem checked3087 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3087 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3087]
  exact B3087.sound accepted3087
#print axioms checked3087

def B3126 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3126 : B3126.tree = HexagonCover.NBand.M7300_7500.SplitData.node3126 := by
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

def B3125 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3126]
theorem treeEq3125 : B3125.tree = HexagonCover.NBand.M7300_7500.SplitData.node3125 := by
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
  · exact treeEq3126

def B3124 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3125, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3124 : B3124.tree = HexagonCover.NBand.M7300_7500.SplitData.node3124 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3125
  · rfl
  · rfl

def B3123 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3124, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3123 : B3123.tree = HexagonCover.NBand.M7300_7500.SplitData.node3123 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3124
  · rfl

def B3122 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3123, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3122 : B3122.tree = HexagonCover.NBand.M7300_7500.SplitData.node3122 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3123
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3121 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3122]
theorem treeEq3121 : B3121.tree = HexagonCover.NBand.M7300_7500.SplitData.node3121 := by
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
  · exact treeEq3122

def B3120 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3121, (.leaf 0 [] 0)]
theorem treeEq3120 : B3120.tree = HexagonCover.NBand.M7300_7500.SplitData.node3120 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3121
  · rfl

def B3119 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3120, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3119 : B3119.tree = HexagonCover.NBand.M7300_7500.SplitData.node3119 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3120
  · rfl

def B3118 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3119, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3118 : B3118.tree = HexagonCover.NBand.M7300_7500.SplitData.node3118 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3119
  · rfl
  · rfl

def B3117 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3118]
theorem treeEq3117 : B3117.tree = HexagonCover.NBand.M7300_7500.SplitData.node3117 := by
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
  · exact treeEq3118

def B3134 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3134 : B3134.tree = HexagonCover.NBand.M7300_7500.SplitData.node3134 := by
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

def B3133 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), B3134, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3133 : B3133.tree = HexagonCover.NBand.M7300_7500.SplitData.node3133 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3134
  · rfl
  · rfl

def B3132 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3133]
theorem treeEq3132 : B3132.tree = HexagonCover.NBand.M7300_7500.SplitData.node3132 := by
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
  · exact treeEq3133

def B3131 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3132, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3131 : B3131.tree = HexagonCover.NBand.M7300_7500.SplitData.node3131 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3132
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3130 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3131]
theorem treeEq3130 : B3130.tree = HexagonCover.NBand.M7300_7500.SplitData.node3130 := by
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
  · exact treeEq3131

def B3129 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3130, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3129 : B3129.tree = HexagonCover.NBand.M7300_7500.SplitData.node3129 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3130
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3128 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3129, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3128 : B3128.tree = HexagonCover.NBand.M7300_7500.SplitData.node3128 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3129
  · rfl

def B3127 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3128, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3127 : B3127.tree = HexagonCover.NBand.M7300_7500.SplitData.node3127 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3128
  · rfl
  · rfl

def B3116 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3117, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3127]
theorem treeEq3116 : B3116.tree = HexagonCover.NBand.M7300_7500.SplitData.node3116 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3117
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3127

theorem accepted3116 : B3116.accepted = true := by decide +kernel
theorem checked3116 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3116 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3116]
  exact B3116.sound accepted3116
#print axioms checked3116

def Tip3086_3087 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3087 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3087
def B3114 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3114 : B3114.tree = HexagonCover.NBand.M7300_7500.SplitData.node3114 := by
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

def B3113 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3114]
theorem treeEq3113 : B3113.tree = HexagonCover.NBand.M7300_7500.SplitData.node3113 := by
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
  · exact treeEq3114

def B3112 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3113, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3112 : B3112.tree = HexagonCover.NBand.M7300_7500.SplitData.node3112 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3113
  · rfl
  · rfl

def B3111 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3112, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3111 : B3111.tree = HexagonCover.NBand.M7300_7500.SplitData.node3111 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3112
  · rfl

def B3110 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3111, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3110 : B3110.tree = HexagonCover.NBand.M7300_7500.SplitData.node3110 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3111
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3109 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3110]
theorem treeEq3109 : B3109.tree = HexagonCover.NBand.M7300_7500.SplitData.node3109 := by
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
  · exact treeEq3110

def B3108 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3109, (.leaf 0 [] 0)]
theorem treeEq3108 : B3108.tree = HexagonCover.NBand.M7300_7500.SplitData.node3108 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3109
  · rfl

def B3107 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3108, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3107 : B3107.tree = HexagonCover.NBand.M7300_7500.SplitData.node3107 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3108
  · rfl

def B3106 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3107, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3106 : B3106.tree = HexagonCover.NBand.M7300_7500.SplitData.node3106 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3107
  · rfl
  · rfl

def B3086 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3086_3087, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3106]
theorem treeEq3086 : B3086.tree = HexagonCover.NBand.M7300_7500.SplitData.node3086 := by
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
  · exact treeEq3106

theorem accepted3086 : B3086.accepted = true := by decide +kernel
theorem checked3086 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3086 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3086]
  exact B3086.sound accepted3086
#print axioms checked3086

def Tip3085_3116 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3116 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3116
def Tip3085_3086 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3086 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3086
def B3143 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3143 : B3143.tree = HexagonCover.NBand.M7300_7500.SplitData.node3143 := by
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

def B3142 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3143]
theorem treeEq3142 : B3142.tree = HexagonCover.NBand.M7300_7500.SplitData.node3142 := by
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
  · exact treeEq3143

def B3141 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3142, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3141 : B3141.tree = HexagonCover.NBand.M7300_7500.SplitData.node3141 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3142
  · rfl
  · rfl

def B3140 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3141, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3140 : B3140.tree = HexagonCover.NBand.M7300_7500.SplitData.node3140 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3141
  · rfl

def B3139 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3140, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3139 : B3139.tree = HexagonCover.NBand.M7300_7500.SplitData.node3139 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3140
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3138 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3139]
theorem treeEq3138 : B3138.tree = HexagonCover.NBand.M7300_7500.SplitData.node3138 := by
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
  · exact treeEq3139

def B3137 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3138, (.leaf 0 [] 0)]
theorem treeEq3137 : B3137.tree = HexagonCover.NBand.M7300_7500.SplitData.node3137 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3138
  · rfl

def B3136 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3137, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3136 : B3136.tree = HexagonCover.NBand.M7300_7500.SplitData.node3136 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3137
  · rfl

def B3135 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3136, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3135 : B3135.tree = HexagonCover.NBand.M7300_7500.SplitData.node3135 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3136
  · rfl
  · rfl

def B3115 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3085_3116, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3135]
theorem treeEq3115 : B3115.tree = HexagonCover.NBand.M7300_7500.SplitData.node3115 := by
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
  · exact treeEq3135

def B3085 : Block := .branch 74 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip3085_3086, B3115, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3085 : B3085.tree = HexagonCover.NBand.M7300_7500.SplitData.node3085 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3115
  · rfl
  · rfl
  · rfl

theorem accepted3085 : B3085.accepted = true := by decide +kernel
theorem checked3085 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3085 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3085]
  exact B3085.sound accepted3085
#print axioms checked3085

end HexagonCover.NBand.M7300_7500.SplitTree.Run0043
