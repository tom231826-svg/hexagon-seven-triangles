import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0045
import HexagonCover.NBand.M7300_7500.SplitTree.Run0046
import HexagonCover.NBand.M7300_7500.SplitTree.Run0047
import HexagonCover.NBand.M7300_7500.SplitTree.Run0048
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0049
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip3418_3449 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3449 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0048.checked3449
def Tip3418_3419 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3419 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0048.checked3419
def B3476 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3476 : B3476.tree = HexagonCover.NBand.M7300_7500.SplitData.node3476 := by
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

def B3475 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3476]
theorem treeEq3475 : B3475.tree = HexagonCover.NBand.M7300_7500.SplitData.node3475 := by
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
  · exact treeEq3476

def B3474 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3475, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3474 : B3474.tree = HexagonCover.NBand.M7300_7500.SplitData.node3474 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3475
  · rfl
  · rfl

def B3473 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3474, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3473 : B3473.tree = HexagonCover.NBand.M7300_7500.SplitData.node3473 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3474
  · rfl

def B3472 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3473, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3472 : B3472.tree = HexagonCover.NBand.M7300_7500.SplitData.node3472 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3473
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3471 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3472]
theorem treeEq3471 : B3471.tree = HexagonCover.NBand.M7300_7500.SplitData.node3471 := by
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
  · exact treeEq3472

def B3470 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3471, (.leaf 0 [] 0)]
theorem treeEq3470 : B3470.tree = HexagonCover.NBand.M7300_7500.SplitData.node3470 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3471
  · rfl

def B3469 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3470, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3469 : B3469.tree = HexagonCover.NBand.M7300_7500.SplitData.node3469 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3470
  · rfl

def B3468 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3469, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3468 : B3468.tree = HexagonCover.NBand.M7300_7500.SplitData.node3468 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3469
  · rfl
  · rfl

def B3448 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3418_3449, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3468]
theorem treeEq3448 : B3448.tree = HexagonCover.NBand.M7300_7500.SplitData.node3448 := by
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
  · exact treeEq3468

def B3418 : Block := .branch 74 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip3418_3419, B3448, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3418 : B3418.tree = HexagonCover.NBand.M7300_7500.SplitData.node3418 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3448
  · rfl
  · rfl
  · rfl

theorem accepted3418 : B3418.accepted = true := by decide +kernel
theorem checked3418 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3418 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3418]
  exact B3418.sound accepted3418
#print axioms checked3418

def Tip3298_3389 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3389 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0047.checked3389
def Tip3298_3359 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3359 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0047.checked3359
def Tip3298_3299 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3299 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0047.checked3299
def B3416 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3416 : B3416.tree = HexagonCover.NBand.M7300_7500.SplitData.node3416 := by
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

def B3415 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3416]
theorem treeEq3415 : B3415.tree = HexagonCover.NBand.M7300_7500.SplitData.node3415 := by
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
  · exact treeEq3416

def B3414 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3415, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3414 : B3414.tree = HexagonCover.NBand.M7300_7500.SplitData.node3414 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3415
  · rfl
  · rfl

def B3413 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3414, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3413 : B3413.tree = HexagonCover.NBand.M7300_7500.SplitData.node3413 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3414
  · rfl

def B3412 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3413, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3412 : B3412.tree = HexagonCover.NBand.M7300_7500.SplitData.node3412 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3413
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3411 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3412]
theorem treeEq3411 : B3411.tree = HexagonCover.NBand.M7300_7500.SplitData.node3411 := by
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
  · exact treeEq3412

def B3410 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3411, (.leaf 0 [] 0)]
theorem treeEq3410 : B3410.tree = HexagonCover.NBand.M7300_7500.SplitData.node3410 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3411
  · rfl

def B3409 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3410, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3409 : B3409.tree = HexagonCover.NBand.M7300_7500.SplitData.node3409 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3410
  · rfl

def B3408 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3409, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3408 : B3408.tree = HexagonCover.NBand.M7300_7500.SplitData.node3408 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3409
  · rfl
  · rfl

def B3388 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3298_3389, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3408]
theorem treeEq3388 : B3388.tree = HexagonCover.NBand.M7300_7500.SplitData.node3388 := by
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
  · exact treeEq3408

def B3358 : Block := .branch 74 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip3298_3359, B3388, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3358 : B3358.tree = HexagonCover.NBand.M7300_7500.SplitData.node3358 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3388
  · rfl
  · rfl
  · rfl

def B3298 : Block := .branch 73 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip3298_3299, B3358, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq3298 : B3298.tree = HexagonCover.NBand.M7300_7500.SplitData.node3298 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3358
  · rfl
  · rfl
  · rfl

theorem accepted3298 : B3298.accepted = true := by decide +kernel
theorem checked3298 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3298 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3298]
  exact B3298.sound accepted3298
#print axioms checked3298

def Tip3297_3508 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3508 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0048.checked3508
def Tip3297_3478 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3478 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0048.checked3478
def Tip3297_3418 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3418 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3418
def Tip3297_3298 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3298 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3298
def B3535 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3535 : B3535.tree = HexagonCover.NBand.M7300_7500.SplitData.node3535 := by
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

def B3534 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3535]
theorem treeEq3534 : B3534.tree = HexagonCover.NBand.M7300_7500.SplitData.node3534 := by
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
  · exact treeEq3535

def B3533 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3534, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3533 : B3533.tree = HexagonCover.NBand.M7300_7500.SplitData.node3533 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3534
  · rfl
  · rfl

def B3532 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3533, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3532 : B3532.tree = HexagonCover.NBand.M7300_7500.SplitData.node3532 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3533
  · rfl

def B3531 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B3532, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3531 : B3531.tree = HexagonCover.NBand.M7300_7500.SplitData.node3531 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3530 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3531]
theorem treeEq3530 : B3530.tree = HexagonCover.NBand.M7300_7500.SplitData.node3530 := by
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
  · exact treeEq3531

def B3529 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3530, (.leaf 0 [] 0)]
theorem treeEq3529 : B3529.tree = HexagonCover.NBand.M7300_7500.SplitData.node3529 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3530
  · rfl

def B3528 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3529, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3528 : B3528.tree = HexagonCover.NBand.M7300_7500.SplitData.node3528 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3529
  · rfl

def B3527 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3528, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3527 : B3527.tree = HexagonCover.NBand.M7300_7500.SplitData.node3527 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3528
  · rfl
  · rfl

def B3507 : Block := .branch 76 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip3297_3508, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B3527]
theorem treeEq3507 : B3507.tree = HexagonCover.NBand.M7300_7500.SplitData.node3507 := by
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
  · exact treeEq3527

def B3477 : Block := .branch 74 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip3297_3478, B3507, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq3477 : B3477.tree = HexagonCover.NBand.M7300_7500.SplitData.node3477 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3507
  · rfl
  · rfl
  · rfl

def B3417 : Block := .branch 73 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip3297_3418, B3477, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq3417 : B3417.tree = HexagonCover.NBand.M7300_7500.SplitData.node3417 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3477
  · rfl
  · rfl
  · rfl

def B3297 : Block := .branch 72 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip3297_3298, B3417, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq3297 : B3297.tree = HexagonCover.NBand.M7300_7500.SplitData.node3297 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3417
  · rfl
  · rfl
  · rfl

theorem accepted3297 : B3297.accepted = true := by decide +kernel
theorem checked3297 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3297 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3297]
  exact B3297.sound accepted3297
#print axioms checked3297

def Tip2921_3161 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3161 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0045.checked3161
def Tip2921_2922 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2922 ![385, 147790266109278553602, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0046.checked2922
def B3288 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq3288 : B3288.tree = HexagonCover.NBand.M7300_7500.SplitData.node3288 := by
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

def B3287 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B3288, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq3287 : B3287.tree = HexagonCover.NBand.M7300_7500.SplitData.node3287 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3288
  · rfl
  · rfl

def B3286 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3287]
theorem treeEq3286 : B3286.tree = HexagonCover.NBand.M7300_7500.SplitData.node3286 := by
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
  · exact treeEq3287

def B3285 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![B3286, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq3285 : B3285.tree = HexagonCover.NBand.M7300_7500.SplitData.node3285 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3286
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3284 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 723).pointIds 723), B3285, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3284 : B3284.tree = HexagonCover.NBand.M7300_7500.SplitData.node3284 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3285
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3283 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3284]
theorem treeEq3283 : B3283.tree = HexagonCover.NBand.M7300_7500.SplitData.node3283 := by
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
  · exact treeEq3284

def B3282 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![B3283, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq3282 : B3282.tree = HexagonCover.NBand.M7300_7500.SplitData.node3282 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3283
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3281 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3282, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3281 : B3281.tree = HexagonCover.NBand.M7300_7500.SplitData.node3281 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3282
  · rfl

def B3280 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3281, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq3280 : B3280.tree = HexagonCover.NBand.M7300_7500.SplitData.node3280 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3281
  · rfl
  · rfl

def B3160 : Block := .branch 68 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip2921_3161, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B3280]
theorem treeEq3160 : B3160.tree = HexagonCover.NBand.M7300_7500.SplitData.node3160 := by
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
  · exact treeEq3280

def B3159 : Block := .branch 91 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B3160, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq3159 : B3159.tree = HexagonCover.NBand.M7300_7500.SplitData.node3159 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3160
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3158 : Block := .branch 113 ![385, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B3159, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq3158 : B3158.tree = HexagonCover.NBand.M7300_7500.SplitData.node3158 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3159
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3157 : Block := .branch 135 ![385, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B3158, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq3157 : B3157.tree = HexagonCover.NBand.M7300_7500.SplitData.node3157 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3158
  · rfl

def B3156 : Block := .branch 138 ![385, 216313519602140674, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B3157, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq3156 : B3156.tree = HexagonCover.NBand.M7300_7500.SplitData.node3156 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3157
  · rfl
  · rfl

def B3155 : Block := .branch 144 ![385, 216313519602140674, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B3156, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq3155 : B3155.tree = HexagonCover.NBand.M7300_7500.SplitData.node3155 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3156
  · rfl

def B3154 : Block := .branch 149 ![385, 216313519602140674, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B3155, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq3154 : B3154.tree = HexagonCover.NBand.M7300_7500.SplitData.node3154 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3155
  · rfl
  · rfl

def B3153 : Block := .branch 161 ![385, 216313519602140674, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 841).pointIds 841), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B3154]
theorem treeEq3153 : B3153.tree = HexagonCover.NBand.M7300_7500.SplitData.node3153 := by
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
  · exact treeEq3154

def B2921 : Block := .branch 72 ![385, 147790266109278553602, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip2921_2922, B3153, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq2921 : B2921.tree = HexagonCover.NBand.M7300_7500.SplitData.node2921 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3153
  · rfl
  · rfl
  · rfl

theorem accepted2921 : B2921.accepted = true := by decide +kernel
theorem checked2921 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2921 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq2921]
  exact B2921.sound accepted2921
#print axioms checked2921

def Tip2920_3297 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3297 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked3297
def Tip2920_2921 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2921 ![385, 147790266109278553602, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked2921
def B3544 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq3544 : B3544.tree = HexagonCover.NBand.M7300_7500.SplitData.node3544 := by
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

def B3543 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), B3544, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq3543 : B3543.tree = HexagonCover.NBand.M7300_7500.SplitData.node3543 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3544
  · rfl
  · rfl

def B3542 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 393248, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3543]
theorem treeEq3542 : B3542.tree = HexagonCover.NBand.M7300_7500.SplitData.node3542 := by
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
  · exact treeEq3543

def B3541 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![B3542, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq3541 : B3541.tree = HexagonCover.NBand.M7300_7500.SplitData.node3541 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3542
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3540 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 723).pointIds 723), B3541, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3540 : B3540.tree = HexagonCover.NBand.M7300_7500.SplitData.node3540 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3541
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3539 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3540]
theorem treeEq3539 : B3539.tree = HexagonCover.NBand.M7300_7500.SplitData.node3539 := by
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
  · exact treeEq3540

def B3538 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![B3539, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq3538 : B3538.tree = HexagonCover.NBand.M7300_7500.SplitData.node3538 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3539
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3537 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3538, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3537 : B3537.tree = HexagonCover.NBand.M7300_7500.SplitData.node3537 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3538
  · rfl

def B3536 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3537, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq3536 : B3536.tree = HexagonCover.NBand.M7300_7500.SplitData.node3536 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3537
  · rfl
  · rfl

def B3296 : Block := .branch 68 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip2920_3297, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B3536]
theorem treeEq3296 : B3296.tree = HexagonCover.NBand.M7300_7500.SplitData.node3296 := by
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
  · exact treeEq3536

def B3295 : Block := .branch 91 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B3296, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq3295 : B3295.tree = HexagonCover.NBand.M7300_7500.SplitData.node3295 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3296
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3294 : Block := .branch 113 ![385, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B3295, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq3294 : B3294.tree = HexagonCover.NBand.M7300_7500.SplitData.node3294 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3295
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3293 : Block := .branch 135 ![385, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B3294, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq3293 : B3293.tree = HexagonCover.NBand.M7300_7500.SplitData.node3293 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3294
  · rfl

def B3292 : Block := .branch 138 ![385, 216313519602140674, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B3293, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq3292 : B3292.tree = HexagonCover.NBand.M7300_7500.SplitData.node3292 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3293
  · rfl
  · rfl

def B3291 : Block := .branch 144 ![385, 216313519602140674, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B3292, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq3291 : B3291.tree = HexagonCover.NBand.M7300_7500.SplitData.node3291 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3292
  · rfl

def B3290 : Block := .branch 149 ![385, 216313519602140674, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B3291, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq3290 : B3290.tree = HexagonCover.NBand.M7300_7500.SplitData.node3290 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3291
  · rfl
  · rfl

def B3289 : Block := .branch 161 ![385, 216313519602140674, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B3290]
theorem treeEq3289 : B3289.tree = HexagonCover.NBand.M7300_7500.SplitData.node3289 := by
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
  · exact treeEq3290

def B2920 : Block := .branch 71 ![385, 147790266109278553602, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip2920_2921, B3289, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq2920 : B2920.tree = HexagonCover.NBand.M7300_7500.SplitData.node2920 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3289
  · rfl
  · rfl
  · rfl

theorem accepted2920 : B2920.accepted = true := by decide +kernel
theorem checked2920 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2920 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq2920]
  exact B2920.sound accepted2920
#print axioms checked2920

end HexagonCover.NBand.M7300_7500.SplitTree.Run0049
