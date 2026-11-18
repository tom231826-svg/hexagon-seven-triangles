import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0064
import HexagonCover.NBand.M7300_7500.SplitTree.Run0066
import HexagonCover.NBand.M7300_7500.SplitTree.Run0067
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0068
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip4637_4728 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4728 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0066.checked4728
def Tip4637_4698 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4698 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0066.checked4698
def Tip4637_4638 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4638 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0066.checked4638
def B4755 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq4755 : B4755.tree = HexagonCover.NBand.M7300_7500.SplitData.node4755 := by
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

def B4754 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4755]
theorem treeEq4754 : B4754.tree = HexagonCover.NBand.M7300_7500.SplitData.node4754 := by
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
  · exact treeEq4755

def B4753 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4754, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4753 : B4753.tree = HexagonCover.NBand.M7300_7500.SplitData.node4753 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4754
  · rfl
  · rfl

def B4752 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4753, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq4752 : B4752.tree = HexagonCover.NBand.M7300_7500.SplitData.node4752 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4753
  · rfl

def B4751 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B4752, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq4751 : B4751.tree = HexagonCover.NBand.M7300_7500.SplitData.node4751 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4752
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4750 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4751]
theorem treeEq4750 : B4750.tree = HexagonCover.NBand.M7300_7500.SplitData.node4750 := by
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
  · exact treeEq4751

def B4749 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4750, (.leaf 0 [] 0)]
theorem treeEq4749 : B4749.tree = HexagonCover.NBand.M7300_7500.SplitData.node4749 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4750
  · rfl

def B4748 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4749, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4748 : B4748.tree = HexagonCover.NBand.M7300_7500.SplitData.node4748 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4749
  · rfl

def B4747 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4748, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq4747 : B4747.tree = HexagonCover.NBand.M7300_7500.SplitData.node4747 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4748
  · rfl
  · rfl

def B4727 : Block := .branch 76 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip4637_4728, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B4747]
theorem treeEq4727 : B4727.tree = HexagonCover.NBand.M7300_7500.SplitData.node4727 := by
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
  · exact treeEq4747

def B4697 : Block := .branch 74 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip4637_4698, B4727, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq4697 : B4697.tree = HexagonCover.NBand.M7300_7500.SplitData.node4697 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4727
  · rfl
  · rfl
  · rfl

def B4637 : Block := .branch 73 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip4637_4638, B4697, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq4637 : B4637.tree = HexagonCover.NBand.M7300_7500.SplitData.node4637 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4697
  · rfl
  · rfl
  · rfl

theorem accepted4637 : B4637.accepted = true := by decide +kernel
theorem checked4637 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4637 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4637]
  exact B4637.sound accepted4637
#print axioms checked4637

def Tip4636_4847 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4847 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0067.checked4847
def Tip4636_4817 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4817 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0067.checked4817
def Tip4636_4757 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4757 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0067.checked4757
def Tip4636_4637 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4637 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked4637
def B4874 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq4874 : B4874.tree = HexagonCover.NBand.M7300_7500.SplitData.node4874 := by
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

def B4873 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4874]
theorem treeEq4873 : B4873.tree = HexagonCover.NBand.M7300_7500.SplitData.node4873 := by
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
  · exact treeEq4874

def B4872 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4873, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4872 : B4872.tree = HexagonCover.NBand.M7300_7500.SplitData.node4872 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4873
  · rfl
  · rfl

def B4871 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4872, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq4871 : B4871.tree = HexagonCover.NBand.M7300_7500.SplitData.node4871 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4872
  · rfl

def B4870 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B4871, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq4870 : B4870.tree = HexagonCover.NBand.M7300_7500.SplitData.node4870 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4871
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4869 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4870]
theorem treeEq4869 : B4869.tree = HexagonCover.NBand.M7300_7500.SplitData.node4869 := by
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
  · exact treeEq4870

def B4868 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4869, (.leaf 0 [] 0)]
theorem treeEq4868 : B4868.tree = HexagonCover.NBand.M7300_7500.SplitData.node4868 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4869
  · rfl

def B4867 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4868, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4867 : B4867.tree = HexagonCover.NBand.M7300_7500.SplitData.node4867 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4868
  · rfl

def B4866 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4867, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq4866 : B4866.tree = HexagonCover.NBand.M7300_7500.SplitData.node4866 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4867
  · rfl
  · rfl

def B4846 : Block := .branch 76 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip4636_4847, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B4866]
theorem treeEq4846 : B4846.tree = HexagonCover.NBand.M7300_7500.SplitData.node4846 := by
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
  · exact treeEq4866

def B4816 : Block := .branch 74 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip4636_4817, B4846, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq4816 : B4816.tree = HexagonCover.NBand.M7300_7500.SplitData.node4816 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4846
  · rfl
  · rfl
  · rfl

def B4756 : Block := .branch 73 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip4636_4757, B4816, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq4756 : B4756.tree = HexagonCover.NBand.M7300_7500.SplitData.node4756 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4816
  · rfl
  · rfl
  · rfl

def B4636 : Block := .branch 72 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip4636_4637, B4756, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq4636 : B4636.tree = HexagonCover.NBand.M7300_7500.SplitData.node4636 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4756
  · rfl
  · rfl
  · rfl

theorem accepted4636 : B4636.accepted = true := by decide +kernel
theorem checked4636 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4636 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4636]
  exact B4636.sound accepted4636
#print axioms checked4636

def Tip4260_4500 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4500 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0064.checked4500
def Tip4260_4261 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4261 ![385, 147790125371790198274, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0064.checked4261
def B4627 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq4627 : B4627.tree = HexagonCover.NBand.M7300_7500.SplitData.node4627 := by
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

def B4626 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B4627, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq4626 : B4626.tree = HexagonCover.NBand.M7300_7500.SplitData.node4626 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4627
  · rfl
  · rfl

def B4625 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 393248, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4626]
theorem treeEq4625 : B4625.tree = HexagonCover.NBand.M7300_7500.SplitData.node4625 := by
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
  · exact treeEq4626

def B4624 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![B4625, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq4624 : B4624.tree = HexagonCover.NBand.M7300_7500.SplitData.node4624 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4625
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4623 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 723).pointIds 723), B4624, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq4623 : B4623.tree = HexagonCover.NBand.M7300_7500.SplitData.node4623 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4624
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4622 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4623]
theorem treeEq4622 : B4622.tree = HexagonCover.NBand.M7300_7500.SplitData.node4622 := by
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
  · exact treeEq4623

def B4621 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![B4622, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq4621 : B4621.tree = HexagonCover.NBand.M7300_7500.SplitData.node4621 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4622
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4620 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4621, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4620 : B4620.tree = HexagonCover.NBand.M7300_7500.SplitData.node4620 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4621
  · rfl

def B4619 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4620, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq4619 : B4619.tree = HexagonCover.NBand.M7300_7500.SplitData.node4619 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4620
  · rfl
  · rfl

def B4499 : Block := .branch 68 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip4260_4500, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B4619]
theorem treeEq4499 : B4499.tree = HexagonCover.NBand.M7300_7500.SplitData.node4499 := by
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
  · exact treeEq4619

def B4498 : Block := .branch 91 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B4499, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq4498 : B4498.tree = HexagonCover.NBand.M7300_7500.SplitData.node4498 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4499
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4497 : Block := .branch 113 ![385, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B4498, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq4497 : B4497.tree = HexagonCover.NBand.M7300_7500.SplitData.node4497 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4498
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4496 : Block := .branch 135 ![385, 216172782113785346, 18446745173221185540, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B4497, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq4496 : B4496.tree = HexagonCover.NBand.M7300_7500.SplitData.node4496 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4497
  · rfl

def B4495 : Block := .branch 138 ![385, 216172782113785346, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B4496, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq4495 : B4495.tree = HexagonCover.NBand.M7300_7500.SplitData.node4495 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4496
  · rfl
  · rfl

def B4494 : Block := .branch 144 ![385, 216172782113785346, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B4495, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq4494 : B4494.tree = HexagonCover.NBand.M7300_7500.SplitData.node4494 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4495
  · rfl

def B4493 : Block := .branch 149 ![385, 216172782113785346, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B4494, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq4493 : B4493.tree = HexagonCover.NBand.M7300_7500.SplitData.node4493 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4494
  · rfl
  · rfl

def B4492 : Block := .branch 161 ![385, 216172782113785346, 18446745173221185540, 79266852862858488596779786248, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 841).pointIds 841), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B4493]
theorem treeEq4492 : B4492.tree = HexagonCover.NBand.M7300_7500.SplitData.node4492 := by
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
  · exact treeEq4493

def B4260 : Block := .branch 72 ![385, 147790125371790198274, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip4260_4261, B4492, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq4260 : B4260.tree = HexagonCover.NBand.M7300_7500.SplitData.node4260 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4492
  · rfl
  · rfl
  · rfl

theorem accepted4260 : B4260.accepted = true := by decide +kernel
theorem checked4260 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4260 (maskNeeds ![385, 147790125371790198274, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4260]
  exact B4260.sound accepted4260
#print axioms checked4260

def Tip4259_4636 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4636 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked4636
def Tip4259_4260 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4260 ![385, 147790125371790198274, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked4260
def B4883 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq4883 : B4883.tree = HexagonCover.NBand.M7300_7500.SplitData.node4883 := by
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

def B4882 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), B4883, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq4882 : B4882.tree = HexagonCover.NBand.M7300_7500.SplitData.node4882 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4883
  · rfl
  · rfl

def B4881 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 98320, 393248, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4882]
theorem treeEq4881 : B4881.tree = HexagonCover.NBand.M7300_7500.SplitData.node4881 := by
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
  · exact treeEq4882

def B4880 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![B4881, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq4880 : B4880.tree = HexagonCover.NBand.M7300_7500.SplitData.node4880 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4881
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4879 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 723).pointIds 723), B4880, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq4879 : B4879.tree = HexagonCover.NBand.M7300_7500.SplitData.node4879 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4880
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4878 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4879]
theorem treeEq4878 : B4878.tree = HexagonCover.NBand.M7300_7500.SplitData.node4878 := by
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
  · exact treeEq4879

def B4877 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![B4878, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq4877 : B4877.tree = HexagonCover.NBand.M7300_7500.SplitData.node4877 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4878
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4876 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4877, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4876 : B4876.tree = HexagonCover.NBand.M7300_7500.SplitData.node4876 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4877
  · rfl

def B4875 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4876, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq4875 : B4875.tree = HexagonCover.NBand.M7300_7500.SplitData.node4875 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4876
  · rfl
  · rfl

def B4635 : Block := .branch 68 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip4259_4636, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B4875]
theorem treeEq4635 : B4635.tree = HexagonCover.NBand.M7300_7500.SplitData.node4635 := by
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
  · exact treeEq4875

def B4634 : Block := .branch 91 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B4635, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq4634 : B4634.tree = HexagonCover.NBand.M7300_7500.SplitData.node4634 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4635
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4633 : Block := .branch 113 ![385, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B4634, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq4633 : B4633.tree = HexagonCover.NBand.M7300_7500.SplitData.node4633 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4634
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4632 : Block := .branch 135 ![385, 216172782113785346, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B4633, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq4632 : B4632.tree = HexagonCover.NBand.M7300_7500.SplitData.node4632 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4633
  · rfl

def B4631 : Block := .branch 138 ![385, 216172782113785346, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B4632, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq4631 : B4631.tree = HexagonCover.NBand.M7300_7500.SplitData.node4631 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4632
  · rfl
  · rfl

def B4630 : Block := .branch 144 ![385, 216172782113785346, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B4631, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq4630 : B4630.tree = HexagonCover.NBand.M7300_7500.SplitData.node4630 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4631
  · rfl

def B4629 : Block := .branch 149 ![385, 216172782113785346, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B4630, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq4629 : B4629.tree = HexagonCover.NBand.M7300_7500.SplitData.node4629 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4630
  · rfl
  · rfl

def B4628 : Block := .branch 161 ![385, 216172782113785346, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B4629]
theorem treeEq4628 : B4628.tree = HexagonCover.NBand.M7300_7500.SplitData.node4628 := by
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
  · exact treeEq4629

def B4259 : Block := .branch 71 ![385, 147790125371790198274, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip4259_4260, B4628, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq4259 : B4259.tree = HexagonCover.NBand.M7300_7500.SplitData.node4259 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4628
  · rfl
  · rfl
  · rfl

theorem accepted4259 : B4259.accepted = true := by decide +kernel
theorem checked4259 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4259 (maskNeeds ![385, 147790125371790198274, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4259]
  exact B4259.sound accepted4259
#print axioms checked4259

def Tip4254_4259 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4259 ![385, 147790125371790198274, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked4259
def B4256 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 936).pointIds 936), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 935).pointIds 935)]
theorem treeEq4256 : B4256.tree = HexagonCover.NBand.M7300_7500.SplitData.node4256 := by
  change Tree.branch (102 : Fin 172) _ = Tree.branch (102 : Fin 172) _
  apply congrArg (Tree.branch (102 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4255 : Block := .branch 168 ![576460752303423873, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4256]
theorem treeEq4255 : B4255.tree = HexagonCover.NBand.M7300_7500.SplitData.node4255 := by
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
  · exact treeEq4256

def B4890 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq4890 : B4890.tree = HexagonCover.NBand.M7300_7500.SplitData.node4890 := by
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
  · rfl

def B4889 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![B4890, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 981).pointIds 981)]
theorem treeEq4889 : B4889.tree = HexagonCover.NBand.M7300_7500.SplitData.node4889 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4890
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4888 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 753).pointIds 753), B4889, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq4888 : B4888.tree = HexagonCover.NBand.M7300_7500.SplitData.node4888 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4889
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4887 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4888]
theorem treeEq4887 : B4887.tree = HexagonCover.NBand.M7300_7500.SplitData.node4887 := by
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
  · exact treeEq4888

def B4886 : Block := .branch 169 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![B4887, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 980).pointIds 980)]
theorem treeEq4886 : B4886.tree = HexagonCover.NBand.M7300_7500.SplitData.node4886 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4887
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4885 : Block := .branch 170 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4886, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4885 : B4885.tree = HexagonCover.NBand.M7300_7500.SplitData.node4885 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4886
  · rfl

def B4884 : Block := .branch 171 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4885, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq4884 : B4884.tree = HexagonCover.NBand.M7300_7500.SplitData.node4884 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4885
  · rfl
  · rfl

def B4258 : Block := .branch 67 ![385, 216172782113785346, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 198).pointIds 198), Tip4254_4259, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B4884]
theorem treeEq4258 : B4258.tree = HexagonCover.NBand.M7300_7500.SplitData.node4258 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4884

def B4896 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 730750818665451459101842416358141509827966273026, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 753).pointIds 753), (.leaf 1 (Common.fact 983).pointIds 983), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq4896 : B4896.tree = HexagonCover.NBand.M7300_7500.SplitData.node4896 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4895 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 846).pointIds 846), B4896, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq4895 : B4895.tree = HexagonCover.NBand.M7300_7500.SplitData.node4895 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4896
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4894 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4895]
theorem treeEq4894 : B4894.tree = HexagonCover.NBand.M7300_7500.SplitData.node4894 := by
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
  · exact treeEq4895

def B4893 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974311749925714704515727424] ![B4894, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 982).pointIds 982)]
theorem treeEq4893 : B4893.tree = HexagonCover.NBand.M7300_7500.SplitData.node4893 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4894
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4892 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4893, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4892 : B4892.tree = HexagonCover.NBand.M7300_7500.SplitData.node4892 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4893
  · rfl

def B4891 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4892, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4891 : B4891.tree = HexagonCover.NBand.M7300_7500.SplitData.node4891 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4892
  · rfl
  · rfl

def B4257 : Block := .branch 65 ![385, 216172782113785346, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B4258, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B4891]
theorem treeEq4257 : B4257.tree = HexagonCover.NBand.M7300_7500.SplitData.node4257 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4258
  · rfl
  · rfl
  · rfl
  · exact treeEq4891

def B4254 : Block := .branch 59 ![385, 216172782113785346, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B4255, B4257, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq4254 : B4254.tree = HexagonCover.NBand.M7300_7500.SplitData.node4254 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4255
  · exact treeEq4257
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4254 : B4254.accepted = true := by decide +kernel
theorem checked4254 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4254 (maskNeeds ![385, 216172782113785346, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4254]
  exact B4254.sound accepted4254
#print axioms checked4254

end HexagonCover.NBand.M7300_7500.SplitTree.Run0068
