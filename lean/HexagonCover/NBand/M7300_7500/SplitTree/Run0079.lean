import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0040
import HexagonCover.NBand.M7300_7500.SplitTree.Run0041
import HexagonCover.NBand.M7300_7500.SplitTree.Run0068
import HexagonCover.NBand.M7300_7500.SplitTree.Run0078
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0079
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip4921_5369 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5369 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] HexagonCover.NBand.M7300_7500.SplitTree.Run0078.checked5369
def Tip4921_4922 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4922 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0078.checked4922
def B5672 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 1031).pointIds 1031)]
theorem treeEq5672 : B5672.tree = HexagonCover.NBand.M7300_7500.SplitData.node5672 := by
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

def B5671 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577687777217187505884839469332948451855677390880, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5672, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5671 : B5671.tree = HexagonCover.NBand.M7300_7500.SplitData.node5671 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5672
  · rfl
  · rfl

def B5670 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676626844588240573268701473812127674924400672, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 1003).pointIds 1003), B5671, (.leaf 6 (Common.fact 1004).pointIds 1004)]
theorem treeEq5670 : B5670.tree = HexagonCover.NBand.M7300_7500.SplitData.node5670 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5671
  · rfl

def B5669 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![B5670, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq5669 : B5669.tree = HexagonCover.NBand.M7300_7500.SplitData.node5669 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5670
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5668 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 723).pointIds 723), B5669, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq5668 : B5668.tree = HexagonCover.NBand.M7300_7500.SplitData.node5668 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5669
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5667 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5668]
theorem treeEq5667 : B5667.tree = HexagonCover.NBand.M7300_7500.SplitData.node5667 := by
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
  · exact treeEq5668

def B5666 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 1496577676670400731206453392024785761878941255467040, 2923003296439877320298169277554860871796666138688] ![B5667, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq5666 : B5666.tree = HexagonCover.NBand.M7300_7500.SplitData.node5666 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5667
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5665 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B5666, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5665 : B5665.tree = HexagonCover.NBand.M7300_7500.SplitData.node5665 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5666
  · rfl

def B5664 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5665, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq5664 : B5664.tree = HexagonCover.NBand.M7300_7500.SplitData.node5664 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5665
  · rfl
  · rfl

def B5368 : Block := .branch 68 ![10384596192949733827821542456689025, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip4921_5369, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B5664]
theorem treeEq5368 : B5368.tree = HexagonCover.NBand.M7300_7500.SplitData.node5368 := by
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
  · exact treeEq5664

def B5367 : Block := .branch 91 ![10384593717069655257060992658440577, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B5368, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq5367 : B5367.tree = HexagonCover.NBand.M7300_7500.SplitData.node5367 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5368
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5366 : Block := .branch 113 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![B5367, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq5366 : B5366.tree = HexagonCover.NBand.M7300_7500.SplitData.node5366 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5367
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5365 : Block := .branch 135 ![385, 144115188075857410, 18446745173221185540, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B5366, (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq5365 : B5365.tree = HexagonCover.NBand.M7300_7500.SplitData.node5365 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5366
  · rfl

def B5364 : Block := .branch 138 ![385, 144115188075857410, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B5365, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq5364 : B5364.tree = HexagonCover.NBand.M7300_7500.SplitData.node5364 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5365
  · rfl
  · rfl

def B5363 : Block := .branch 144 ![385, 144115188075857410, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B5364, (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq5363 : B5363.tree = HexagonCover.NBand.M7300_7500.SplitData.node5363 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5364
  · rfl

def B5362 : Block := .branch 149 ![385, 144115188075857410, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B5363, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq5362 : B5362.tree = HexagonCover.NBand.M7300_7500.SplitData.node5362 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5363
  · rfl
  · rfl

def B5361 : Block := .branch 161 ![385, 144115188075857410, 18446745173221185540, 79266850501675247161957179400, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B5362]
theorem treeEq5361 : B5361.tree = HexagonCover.NBand.M7300_7500.SplitData.node5361 := by
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
  · exact treeEq5362

def B4921 : Block := .branch 71 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip4921_4922, B5361, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq4921 : B4921.tree = HexagonCover.NBand.M7300_7500.SplitData.node4921 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5361
  · rfl
  · rfl
  · rfl

theorem accepted4921 : B4921.accepted = true := by decide +kernel
theorem checked4921 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4921 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4921]
  exact B4921.sound accepted4921
#print axioms checked4921

def Tip4919_4921 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4921 ![385, 147718067777752270338, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked4921
def B5682 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 783).pointIds 783)]
theorem treeEq5682 : B5682.tree = HexagonCover.NBand.M7300_7500.SplitData.node5682 := by
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

def B5681 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 23384026219072518174517324317865330546450955239488] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B5682, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 911).pointIds 911)]
theorem treeEq5681 : B5681.tree = HexagonCover.NBand.M7300_7500.SplitData.node5681 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5682
  · rfl
  · rfl

def B5680 : Block := .branch 90 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317175958748842277436655106, 6148, 24584, 98320, 393248, 23384026219072518174516086377826045166176056115264] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 1032).pointIds 1032), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), B5681]
theorem treeEq5680 : B5680.tree = HexagonCover.NBand.M7300_7500.SplitData.node5680 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5681

def B5679 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 590295810358705653250, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516086377826045166176056115264] ![(.leaf 0 (Common.fact 605).pointIds 605), B5680, (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq5679 : B5679.tree = HexagonCover.NBand.M7300_7500.SplitData.node5679 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5680
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5678 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 590295810358705653250, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516086377826045166176056115264] ![B5679, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 981).pointIds 981)]
theorem treeEq5678 : B5678.tree = HexagonCover.NBand.M7300_7500.SplitData.node5678 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5679
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5677 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516086377826045166176056115264] ![(.leaf 0 (Common.fact 753).pointIds 753), B5678, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq5677 : B5677.tree = HexagonCover.NBand.M7300_7500.SplitData.node5677 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5678
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5676 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5677]
theorem treeEq5676 : B5676.tree = HexagonCover.NBand.M7300_7500.SplitData.node5676 := by
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
  · exact treeEq5677

def B5675 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![B5676, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 980).pointIds 980)]
theorem treeEq5675 : B5675.tree = HexagonCover.NBand.M7300_7500.SplitData.node5675 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5676
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5674 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B5675, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5674 : B5674.tree = HexagonCover.NBand.M7300_7500.SplitData.node5674 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5675
  · rfl

def B5673 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5674, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq5673 : B5673.tree = HexagonCover.NBand.M7300_7500.SplitData.node5673 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5674
  · rfl
  · rfl

def B4920 : Block := .branch 67 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 198).pointIds 198), Tip4919_4921, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B5673]
theorem treeEq4920 : B4920.tree = HexagonCover.NBand.M7300_7500.SplitData.node4920 := by
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
  · exact treeEq5673

def B5688 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 730750818665451459101842416358141509827966273026, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 753).pointIds 753), (.leaf 1 (Common.fact 983).pointIds 983), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq5688 : B5688.tree = HexagonCover.NBand.M7300_7500.SplitData.node5688 := by
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

def B5687 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 846).pointIds 846), B5688, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq5687 : B5687.tree = HexagonCover.NBand.M7300_7500.SplitData.node5687 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5688
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5686 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5687]
theorem treeEq5686 : B5686.tree = HexagonCover.NBand.M7300_7500.SplitData.node5686 := by
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
  · exact treeEq5687

def B5685 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974311749925714704515727424] ![B5686, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 982).pointIds 982)]
theorem treeEq5685 : B5685.tree = HexagonCover.NBand.M7300_7500.SplitData.node5685 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5686
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5684 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B5685, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5684 : B5684.tree = HexagonCover.NBand.M7300_7500.SplitData.node5684 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5685
  · rfl

def B5683 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5684, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq5683 : B5683.tree = HexagonCover.NBand.M7300_7500.SplitData.node5683 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5684
  · rfl
  · rfl

def B4919 : Block := .branch 65 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B4920, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B5683]
theorem treeEq4919 : B4919.tree = HexagonCover.NBand.M7300_7500.SplitData.node4919 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4920
  · rfl
  · rfl
  · rfl
  · exact treeEq5683

theorem accepted4919 : B4919.accepted = true := by decide +kernel
theorem checked4919 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4919 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4919]
  exact B4919.sound accepted4919
#print axioms checked4919

def Tip4908_4919 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4919 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked4919
def B4918 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072528559109803447333728274579038142528] ![(.leaf 0 (Common.fact 994).pointIds 994), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 995).pointIds 995)]
theorem treeEq4918 : B4918.tree = HexagonCover.NBand.M7300_7500.SplitData.node4918 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4917 : Block := .branch 170 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353602138320208187523989443222265480496644112, 393248, 23384026219072528559743628747447842975327389745216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4918, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4917 : B4917.tree = HexagonCover.NBand.M7300_7500.SplitData.node4917 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4918
  · rfl

def B4916 : Block := .branch 171 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219072528559743628747447842975327389745216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4917, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 993).pointIds 993)]
theorem treeEq4916 : B4916.tree = HexagonCover.NBand.M7300_7500.SplitData.node4916 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4917
  · rfl
  · rfl

def B4915 : Block := .branch 113 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219072518175149911677792585914334731305024] ![(.leaf 0 (Common.fact 992).pointIds 992), (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), B4916]
theorem treeEq4915 : B4915.tree = HexagonCover.NBand.M7300_7500.SplitData.node4915 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4916

def B4914 : Block := .branch 65 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B4915, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq4914 : B4914.tree = HexagonCover.NBand.M7300_7500.SplitData.node4914 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4915
  · rfl
  · rfl
  · rfl
  · rfl

def B4913 : Block := .branch 67 ![576460752303423873, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 198).pointIds 198), B4914, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), (.leaf 6 (Common.fact 986).pointIds 986)]
theorem treeEq4913 : B4913.tree = HexagonCover.NBand.M7300_7500.SplitData.node4913 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4914
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4912 : Block := .branch 138 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B4913, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 985).pointIds 985)]
theorem treeEq4912 : B4912.tree = HexagonCover.NBand.M7300_7500.SplitData.node4912 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4913
  · rfl
  · rfl

def B4911 : Block := .branch 144 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B4912, (.leaf 6 (Common.fact 984).pointIds 984)]
theorem treeEq4911 : B4911.tree = HexagonCover.NBand.M7300_7500.SplitData.node4911 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4912
  · rfl

def B4910 : Block := .branch 124 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219072518175149911677792585914334731305024] ![(.leaf 0 (Common.fact 991).pointIds 991), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B4911]
theorem treeEq4910 : B4910.tree = HexagonCover.NBand.M7300_7500.SplitData.node4910 := by
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
  · exact treeEq4911

def B4909 : Block := .branch 164 ![576460752303423873, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 990).pointIds 990), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4910]
theorem treeEq4909 : B4909.tree = HexagonCover.NBand.M7300_7500.SplitData.node4909 := by
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
  · exact treeEq4910

def B4908 : Block := .branch 59 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B4909, Tip4908_4919, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq4908 : B4908.tree = HexagonCover.NBand.M7300_7500.SplitData.node4908 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4909
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4908 : B4908.accepted = true := by decide +kernel
theorem checked4908 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4908 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4908]
  exact B4908.sound accepted4908
#print axioms checked4908

def Tip4250_4254 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4254 ![385, 216172782113785346, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0068.checked4254
def Tip4250_4908 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4908 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] checked4908
def B4253 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 935).pointIds 935)]
theorem treeEq4253 : B4253.tree = HexagonCover.NBand.M7300_7500.SplitData.node4253 := by
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

def B4252 : Block := .branch 168 ![288230376151712129, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4253]
theorem treeEq4252 : B4252.tree = HexagonCover.NBand.M7300_7500.SplitData.node4252 := by
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
  · exact treeEq4253

def B4251 : Block := .branch 58 ![385, 216172782113785346, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B4252, Tip4250_4254, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq4251 : B4251.tree = HexagonCover.NBand.M7300_7500.SplitData.node4251 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4252
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4907 : Block := .branch 91 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 2993155353275488515612970050411246142768154144145472] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 989).pointIds 989)]
theorem treeEq4907 : B4907.tree = HexagonCover.NBand.M7300_7500.SplitData.node4907 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4906 : Block := .branch 171 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1496577676975293731967614255287969410137805572636688, 393248, 21799339131823513008298518512804296130624] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 965).pointIds 965), (.leaf 5 (Common.fact 656).pointIds 656), B4907]
theorem treeEq4906 : B4906.tree = HexagonCover.NBand.M7300_7500.SplitData.node4906 := by
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
  · exact treeEq4907

def B4905 : Block := .branch 170 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 21799339131823513008298518512804296130624] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4906, (.leaf 5 (Common.fact 988).pointIds 988), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4905 : B4905.tree = HexagonCover.NBand.M7300_7500.SplitData.node4905 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4906
  · rfl
  · rfl

def B4904 : Block := .branch 114 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131823513008298518512804296130624] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 233).pointIds 233), (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), B4905, (.leaf 6 (Common.fact 237).pointIds 237)]
theorem treeEq4904 : B4904.tree = HexagonCover.NBand.M7300_7500.SplitData.node4904 := by
  change Tree.branch (114 : Fin 172) _ = Tree.branch (114 : Fin 172) _
  apply congrArg (Tree.branch (114 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4905
  · rfl

def B4903 : Block := .branch 65 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B4904, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq4903 : B4903.tree = HexagonCover.NBand.M7300_7500.SplitData.node4903 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4904
  · rfl
  · rfl
  · rfl
  · rfl

def B4902 : Block := .branch 67 ![288230376151712129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 198).pointIds 198), B4903, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), (.leaf 6 (Common.fact 986).pointIds 986)]
theorem treeEq4902 : B4902.tree = HexagonCover.NBand.M7300_7500.SplitData.node4902 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4903
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4901 : Block := .branch 138 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B4902, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 985).pointIds 985)]
theorem treeEq4901 : B4901.tree = HexagonCover.NBand.M7300_7500.SplitData.node4901 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4902
  · rfl
  · rfl

def B4900 : Block := .branch 144 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219093785823082470331759046827299216818240] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B4901, (.leaf 6 (Common.fact 984).pointIds 984)]
theorem treeEq4900 : B4900.tree = HexagonCover.NBand.M7300_7500.SplitData.node4900 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4901
  · rfl

def B4899 : Block := .branch 124 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 23384026219072518175149911677792585914334731305024] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B4900]
theorem treeEq4899 : B4899.tree = HexagonCover.NBand.M7300_7500.SplitData.node4899 := by
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
  · exact treeEq4900

def B4898 : Block := .branch 164 ![288230376151712129, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 163).pointIds 163), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4899]
theorem treeEq4898 : B4898.tree = HexagonCover.NBand.M7300_7500.SplitData.node4898 := by
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
  · exact treeEq4899

def B4897 : Block := .branch 58 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B4898, Tip4250_4908, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq4897 : B4897.tree = HexagonCover.NBand.M7300_7500.SplitData.node4897 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4898
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4250 : Block := .branch 56 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 153).pointIds 153), B4251, B4897, (.leaf 3 (Common.fact 154).pointIds 154), (.leaf 4 (Common.fact 155).pointIds 155), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 157).pointIds 157)]
theorem treeEq4250 : B4250.tree = HexagonCover.NBand.M7300_7500.SplitData.node4250 := by
  change Tree.branch (56 : Fin 172) _ = Tree.branch (56 : Fin 172) _
  apply congrArg (Tree.branch (56 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4251
  · exact treeEq4897
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4250 : B4250.accepted = true := by decide +kernel
theorem checked4250 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4250 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4250]
  exact B4250.sound accepted4250
#print axioms checked4250

def Tip0011_2685 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2685 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0040.checked2685
def Tip0011_2498 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2498 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0040.checked2498
def Tip0011_0014 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0014 ![385, 144257025075840514, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] HexagonCover.NBand.M7300_7500.SplitTree.Run0041.checked0014
def B2679 : Block := .branch 91 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq2679 : B2679.tree = HexagonCover.NBand.M7300_7500.SplitData.node2679 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2678 : Block := .branch 171 ![288230376151712129, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2679]
theorem treeEq2678 : B2678.tree = HexagonCover.NBand.M7300_7500.SplitData.node2678 := by
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
  · exact treeEq2679

def B2677 : Block := .branch 170 ![288230376151712129, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2678, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2677 : B2677.tree = HexagonCover.NBand.M7300_7500.SplitData.node2677 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2678
  · rfl
  · rfl

def B2676 : Block := .branch 169 ![288230376151712129, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 800).pointIds 800), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2677, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2676 : B2676.tree = HexagonCover.NBand.M7300_7500.SplitData.node2676 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2677
  · rfl

def B2684 : Block := .branch 91 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 809).pointIds 809), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq2684 : B2684.tree = HexagonCover.NBand.M7300_7500.SplitData.node2684 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2683 : Block := .branch 171 ![576460752303423873, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2684]
theorem treeEq2683 : B2683.tree = HexagonCover.NBand.M7300_7500.SplitData.node2683 := by
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
  · exact treeEq2684

def B2682 : Block := .branch 170 ![576460752303423873, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2683, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2682 : B2682.tree = HexagonCover.NBand.M7300_7500.SplitData.node2682 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2683
  · rfl
  · rfl

def B2681 : Block := .branch 169 ![576460752303423873, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 808).pointIds 808), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2682, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2681 : B2681.tree = HexagonCover.NBand.M7300_7500.SplitData.node2681 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2682
  · rfl

def B2680 : Block := .branch 59 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![B2681, Tip0011_2685, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq2680 : B2680.tree = HexagonCover.NBand.M7300_7500.SplitData.node2680 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2681
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2675 : Block := .branch 58 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![B2676, B2680, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq2675 : B2675.tree = HexagonCover.NBand.M7300_7500.SplitData.node2675 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2676
  · exact treeEq2680
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2497 : Block := .branch 56 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 153).pointIds 153), Tip0011_2498, B2675, (.leaf 3 (Common.fact 154).pointIds 154), (.leaf 4 (Common.fact 155).pointIds 155), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 157).pointIds 157)]
theorem treeEq2497 : B2497.tree = HexagonCover.NBand.M7300_7500.SplitData.node2497 := by
  change Tree.branch (56 : Fin 172) _ = Tree.branch (56 : Fin 172) _
  apply congrArg (Tree.branch (56 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2675
  · rfl
  · rfl
  · rfl
  · rfl

def B2496 : Block := .branch 87 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 849).pointIds 849), (.leaf 3 (Common.fact 125).pointIds 125), (.leaf 4 (Common.fact 126).pointIds 126), (.leaf 5 (Common.fact 127).pointIds 127), B2497]
theorem treeEq2496 : B2496.tree = HexagonCover.NBand.M7300_7500.SplitData.node2496 := by
  change Tree.branch (87 : Fin 172) _ = Tree.branch (87 : Fin 172) _
  apply congrArg (Tree.branch (87 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2497

def B0013 : Block := .branch 47 ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 76).pointIds 76), Tip0011_0014, B2496, (.leaf 3 (Common.fact 77).pointIds 77), (.leaf 4 (Common.fact 78).pointIds 78), (.leaf 5 (Common.fact 79).pointIds 79), (.leaf 6 (Common.fact 80).pointIds 80)]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M7300_7500.SplitData.node0013 := by
  change Tree.branch (47 : Fin 172) _ = Tree.branch (47 : Fin 172) _
  apply congrArg (Tree.branch (47 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2496
  · rfl
  · rfl
  · rfl
  · rfl

def B0012 : Block := .branch 149 ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B0013, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 75).pointIds 75)]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M7300_7500.SplitData.node0012 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0013
  · rfl
  · rfl

def B0011 : Block := .branch 88 ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483890799611827146927305448226880] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 65).pointIds 65), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B0012]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M7300_7500.SplitData.node0011 := by
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
  · exact treeEq0012

theorem accepted0011 : B0011.accepted = true := by decide +kernel
theorem checked0011 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0011 (maskNeeds ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483890799611827146927305448226880]) := by
  rw [← treeEq0011]
  exact B0011.sound accepted0011
#print axioms checked0011

end HexagonCover.NBand.M7300_7500.SplitTree.Run0079
