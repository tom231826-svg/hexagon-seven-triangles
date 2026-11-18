import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0012
import HexagonCover.NBand.M7500_7700.SplitTree.Run0013
import HexagonCover.NBand.M7500_7700.SplitTree.Run0018
import HexagonCover.NBand.M7500_7700.SplitTree.Run0025
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0026
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0011_0591 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0591 ![385, 720716677867636226, 18554830464766449668, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0012.checked0591
def Tip0011_0567 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0567 ![288230376151712129, 144255925564212738, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0012.checked0567
def Tip0011_0030 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0030 ![385, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] HexagonCover.NBand.M7500_7700.SplitTree.Run0012.checked0030
def Tip0011_0012 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0012 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] HexagonCover.NBand.M7500_7700.SplitTree.Run0013.checked0012
def B0590 : Block := .branch 160 ![385, 748288838313422294120286634350736906204574950360578, 18518801667747485700, 24584, 98320, 393248, 21783398779833985787364815188325238833216] ![(.leaf 0 (Common.fact 362).pointIds 362), (.leaf 1 (Common.fact 734).pointIds 734), (.leaf 2 (Common.fact 735).pointIds 735), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 366).pointIds 366)]
theorem treeEq0590 : B0590.tree = HexagonCover.NBand.M7500_7700.SplitData.node0590 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0589 : Block := .branch 169 ![576460752303423873, 140737488356866, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21783398779833985787364815188325238833216] ![(.leaf 0 (Common.fact 731).pointIds 731), B0590, (.leaf 2 (Common.fact 732).pointIds 732), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0589 : B0589.tree = HexagonCover.NBand.M7500_7700.SplitData.node0589 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0590
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0588 : Block := .branch 113 ![576460752303423873, 140737488356866, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21783388395240268717709558127332580393024] ![(.leaf 0 (Common.fact 239).pointIds 239), (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), B0589]
theorem treeEq0588 : B0588.tree = HexagonCover.NBand.M7500_7700.SplitData.node0588 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0589

def B0587 : Block := .branch 65 ![576460752303423873, 140737488356866, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B0588, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0587 : B0587.tree = HexagonCover.NBand.M7500_7700.SplitData.node0587 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0588
  · rfl
  · rfl
  · rfl
  · rfl

def B0586 : Block := .branch 67 ![576460752303423873, 140737488356866, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 233).pointIds 233), B0587, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq0586 : B0586.tree = HexagonCover.NBand.M7500_7700.SplitData.node0586 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0587
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0585 : Block := .branch 122 ![576460752303423873, 140737488356866, 18518801667747485700, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 111).pointIds 111), B0586]
theorem treeEq0585 : B0585.tree = HexagonCover.NBand.M7500_7700.SplitData.node0585 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0586

def B0584 : Block := .branch 138 ![576460752303423873, 140737488356866, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0585, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0584 : B0584.tree = HexagonCover.NBand.M7500_7700.SplitData.node0584 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0585
  · rfl
  · rfl

def B0583 : Block := .branch 144 ![576460752303423873, 140737488356866, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0584, (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0583 : B0583.tree = HexagonCover.NBand.M7500_7700.SplitData.node0583 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0584
  · rfl

def B0582 : Block := .branch 124 ![576460752303423873, 140737488356866, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0583]
theorem treeEq0582 : B0582.tree = HexagonCover.NBand.M7500_7700.SplitData.node0582 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0583

def B0581 : Block := .branch 59 ![385, 144255925564212738, 18554830464766449668, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![B0582, Tip0011_0591, (.leaf 2 (Common.fact 227).pointIds 227), (.leaf 3 (Common.fact 228).pointIds 228), (.leaf 4 (Common.fact 229).pointIds 229), (.leaf 5 (Common.fact 230).pointIds 230), (.leaf 6 (Common.fact 231).pointIds 231)]
theorem treeEq0581 : B0581.tree = HexagonCover.NBand.M7500_7700.SplitData.node0581 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0582
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0566 : Block := .branch 58 ![385, 144255925564212738, 18554830464766449668, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![Tip0011_0567, B0581, (.leaf 2 (Common.fact 167).pointIds 167), (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq0566 : B0566.tree = HexagonCover.NBand.M7500_7700.SplitData.node0566 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0581
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0565 : Block := .branch 87 ![385, 144255925564212738, 18554830464766449668, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 714).pointIds 714), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 122).pointIds 122), (.leaf 5 (Common.fact 123).pointIds 123), B0566]
theorem treeEq0565 : B0565.tree = HexagonCover.NBand.M7500_7700.SplitData.node0565 := by
  change Tree.branch (87 : Fin 173) _ = Tree.branch (87 : Fin 173) _
  apply congrArg (Tree.branch (87 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0566

def B0029 : Block := .branch 56 ![385, 144255925564212738, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 162).pointIds 162), Tip0011_0030, B0565, (.leaf 3 (Common.fact 163).pointIds 163), (.leaf 4 (Common.fact 164).pointIds 164), (.leaf 5 (Common.fact 165).pointIds 165), (.leaf 6 (Common.fact 166).pointIds 166)]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M7500_7700.SplitData.node0029 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0565
  · rfl
  · rfl
  · rfl
  · rfl

def B0028 : Block := .branch 98 ![385, 144255925564212738, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 136).pointIds 136), (.leaf 1 (Common.fact 137).pointIds 137), (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), B0029]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M7500_7700.SplitData.node0028 := by
  change Tree.branch (98 : Fin 173) _ = Tree.branch (98 : Fin 173) _
  apply congrArg (Tree.branch (98 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0029

def B0027 : Block := .branch 85 ![385, 144255925564212738, 18482772870728521732, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 130).pointIds 130), (.leaf 1 (Common.fact 131).pointIds 131), (.leaf 2 (Common.fact 161).pointIds 161), B0028, (.leaf 4 (Common.fact 133).pointIds 133), (.leaf 5 (Common.fact 134).pointIds 134), (.leaf 6 (Common.fact 135).pointIds 135)]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M7500_7700.SplitData.node0027 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0028
  · rfl
  · rfl
  · rfl

def B0011 : Block := .branch 55 ![385, 144255925564212738, 18446744073709557764, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 65).pointIds 65), Tip0011_0012, B0027, (.leaf 3 (Common.fact 66).pointIds 66), (.leaf 4 (Common.fact 67).pointIds 67), (.leaf 5 (Common.fact 68).pointIds 68), (.leaf 6 (Common.fact 69).pointIds 69)]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M7500_7700.SplitData.node0011 := by
  change Tree.branch (55 : Fin 173) _ = Tree.branch (55 : Fin 173) _
  apply congrArg (Tree.branch (55 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0027
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0011 : B0011.accepted = true := by decide +kernel
theorem checked0011 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0011 (maskNeeds ![385, 144255925564212738, 18446744073709557764, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848]) := by
  rw [← treeEq0011]
  exact B0011.sound accepted0011
#print axioms checked0011

def Tip0006_1033 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1033 ![385, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0018.checked1033
def Tip0006_1430 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1430 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0025.checked1430
def Tip0006_0011 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0011 ![385, 144255925564212738, 18446744073709557764, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] checked0011
def B1028 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 333).pointIds 333), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 335).pointIds 335), (.leaf 5 (Common.fact 336).pointIds 336), (.leaf 6 (Common.fact 870).pointIds 870)]
theorem treeEq1028 : B1028.tree = HexagonCover.NBand.M7500_7700.SplitData.node1028 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1027 : Block := .branch 169 ![288230376151712129, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), B1028]
theorem treeEq1027 : B1027.tree = HexagonCover.NBand.M7500_7700.SplitData.node1027 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1028

def B1031 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 333).pointIds 333), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 335).pointIds 335), (.leaf 5 (Common.fact 336).pointIds 336), (.leaf 6 (Common.fact 870).pointIds 870)]
theorem treeEq1031 : B1031.tree = HexagonCover.NBand.M7500_7700.SplitData.node1031 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1030 : Block := .branch 169 ![576460752303423873, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 731).pointIds 731), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), B1031]
theorem treeEq1030 : B1030.tree = HexagonCover.NBand.M7500_7700.SplitData.node1030 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1031

def B1429 : Block := .branch 79 ![1496577676626844588240573268701473812127674924007809, 216172782113785346, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq1429 : B1429.tree = HexagonCover.NBand.M7500_7700.SplitData.node1429 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1428 : Block := .branch 170 ![385, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 21778071483256974311749925714704515727424] ![B1429, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 862).pointIds 862)]
theorem treeEq1428 : B1428.tree = HexagonCover.NBand.M7500_7700.SplitData.node1428 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1429
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1427 : Block := .branch 171 ![385, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1428, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1427 : B1427.tree = HexagonCover.NBand.M7500_7700.SplitData.node1427 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1428
  · rfl

def B1426 : Block := .branch 172 ![385, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1427, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq1426 : B1426.tree = HexagonCover.NBand.M7500_7700.SplitData.node1426 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1427
  · rfl
  · rfl

def B1032 : Block := .branch 65 ![385, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), Tip0006_1033, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B1426]
theorem treeEq1032 : B1032.tree = HexagonCover.NBand.M7500_7700.SplitData.node1032 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1426

def B1029 : Block := .branch 59 ![385, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![B1030, B1032, (.leaf 2 (Common.fact 227).pointIds 227), (.leaf 3 (Common.fact 228).pointIds 228), (.leaf 4 (Common.fact 229).pointIds 229), (.leaf 5 (Common.fact 230).pointIds 230), (.leaf 6 (Common.fact 231).pointIds 231)]
theorem treeEq1029 : B1029.tree = HexagonCover.NBand.M7500_7700.SplitData.node1029 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1030
  · exact treeEq1032
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1026 : Block := .branch 58 ![385, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![B1027, B1029, (.leaf 2 (Common.fact 167).pointIds 167), (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq1026 : B1026.tree = HexagonCover.NBand.M7500_7700.SplitData.node1026 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1027
  · exact treeEq1029
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1025 : Block := .branch 56 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 162).pointIds 162), B1026, Tip0006_1430, (.leaf 3 (Common.fact 163).pointIds 163), (.leaf 4 (Common.fact 164).pointIds 164), (.leaf 5 (Common.fact 165).pointIds 165), (.leaf 6 (Common.fact 166).pointIds 166)]
theorem treeEq1025 : B1025.tree = HexagonCover.NBand.M7500_7700.SplitData.node1025 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1026
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1024 : Block := .branch 98 ![385, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 21778071482940216404160885548717283213376] ![(.leaf 0 (Common.fact 136).pointIds 136), (.leaf 1 (Common.fact 137).pointIds 137), (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), B1025]
theorem treeEq1024 : B1024.tree = HexagonCover.NBand.M7500_7700.SplitData.node1024 := by
  change Tree.branch (98 : Fin 173) _ = Tree.branch (98 : Fin 173) _
  apply congrArg (Tree.branch (98 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1025

def B1023 : Block := .branch 85 ![385, 144115188075857410, 18446884811197913092, 79247505327378171660339273736, 98320, 393248, 21778071482940216404160885548717283213376] ![(.leaf 0 (Common.fact 130).pointIds 130), (.leaf 1 (Common.fact 131).pointIds 131), (.leaf 2 (Common.fact 865).pointIds 865), B1024, (.leaf 4 (Common.fact 133).pointIds 133), (.leaf 5 (Common.fact 134).pointIds 134), (.leaf 6 (Common.fact 135).pointIds 135)]
theorem treeEq1023 : B1023.tree = HexagonCover.NBand.M7500_7700.SplitData.node1023 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1024
  · rfl
  · rfl
  · rfl

def B1022 : Block := .branch 87 ![385, 144115188075857410, 18446884811197913092, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 864).pointIds 864), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 122).pointIds 122), (.leaf 5 (Common.fact 123).pointIds 123), B1023]
theorem treeEq1022 : B1022.tree = HexagonCover.NBand.M7500_7700.SplitData.node1022 := by
  change Tree.branch (87 : Fin 173) _ = Tree.branch (87 : Fin 173) _
  apply congrArg (Tree.branch (87 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1023

def B0010 : Block := .branch 47 ![385, 144115188075857410, 18446744073709557764, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 60).pointIds 60), Tip0006_0011, B1022, (.leaf 3 (Common.fact 61).pointIds 61), (.leaf 4 (Common.fact 62).pointIds 62), (.leaf 5 (Common.fact 63).pointIds 63), (.leaf 6 (Common.fact 64).pointIds 64)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M7500_7700.SplitData.node0010 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1022
  · rfl
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 46 ![385, 144115188075857410, 18446744073709557764, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 54).pointIds 54), (.leaf 1 (Common.fact 55).pointIds 55), B0010, (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M7500_7700.SplitData.node0009 := by
  change Tree.branch (46 : Fin 173) _ = Tree.branch (46 : Fin 173) _
  apply congrArg (Tree.branch (46 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 57 ![385, 1538, 18446744073709557764, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 48).pointIds 48), B0009, (.leaf 2 (Common.fact 49).pointIds 49), (.leaf 3 (Common.fact 50).pointIds 50), (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M7500_7700.SplitData.node0008 := by
  change Tree.branch (57 : Fin 173) _ = Tree.branch (57 : Fin 173) _
  apply congrArg (Tree.branch (57 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 48 ![385, 1538, 18446744073709557764, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 42).pointIds 42), B0008, (.leaf 2 (Common.fact 43).pointIds 43), (.leaf 3 (Common.fact 44).pointIds 44), (.leaf 4 (Common.fact 45).pointIds 45), (.leaf 5 (Common.fact 46).pointIds 46), (.leaf 6 (Common.fact 47).pointIds 47)]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M7500_7700.SplitData.node0007 := by
  change Tree.branch (48 : Fin 173) _ = Tree.branch (48 : Fin 173) _
  apply congrArg (Tree.branch (48 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0008
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0006 : Block := .branch 84 ![385, 1538, 18446744073709557764, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 36).pointIds 36), (.leaf 1 (Common.fact 37).pointIds 37), (.leaf 2 (Common.fact 38).pointIds 38), B0007, (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M7500_7700.SplitData.node0006 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0007
  · rfl
  · rfl
  · rfl

theorem accepted0006 : B0006.accepted = true := by decide +kernel
theorem checked0006 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0006 (maskNeeds ![385, 1538, 18446744073709557764, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848]) := by
  rw [← treeEq0006]
  exact B0006.sound accepted0006
#print axioms checked0006

def Tip0000_0006 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0006 ![385, 1538, 18446744073709557764, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] checked0006
def B0005 : Block := .branch 96 ![385, 1538, 18446744073709557764, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), (.leaf 2 (Common.fact 32).pointIds 32), Tip0000_0006, (.leaf 4 (Common.fact 33).pointIds 33), (.leaf 5 (Common.fact 34).pointIds 34), (.leaf 6 (Common.fact 35).pointIds 35)]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M7500_7700.SplitData.node0005 := by
  change Tree.branch (96 : Fin 173) _ = Tree.branch (96 : Fin 173) _
  apply congrArg (Tree.branch (96 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0004 : Block := .branch 64 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), B0005, (.leaf 3 (Common.fact 26).pointIds 26), (.leaf 4 (Common.fact 27).pointIds 27), (.leaf 5 (Common.fact 28).pointIds 28), (.leaf 6 (Common.fact 29).pointIds 29)]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M7500_7700.SplitData.node0004 := by
  change Tree.branch (64 : Fin 173) _ = Tree.branch (64 : Fin 173) _
  apply congrArg (Tree.branch (64 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0005
  · rfl
  · rfl
  · rfl
  · rfl

def B0003 : Block := .branch 62 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), B0004, (.leaf 3 (Common.fact 20).pointIds 20), (.leaf 4 (Common.fact 21).pointIds 21), (.leaf 5 (Common.fact 22).pointIds 22), (.leaf 6 (Common.fact 23).pointIds 23)]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M7500_7700.SplitData.node0003 := by
  change Tree.branch (62 : Fin 173) _ = Tree.branch (62 : Fin 173) _
  apply congrArg (Tree.branch (62 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0004
  · rfl
  · rfl
  · rfl
  · rfl

def B0002 : Block := .branch 106 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), B0003, (.leaf 4 (Common.fact 15).pointIds 15), (.leaf 5 (Common.fact 16).pointIds 16), (.leaf 6 (Common.fact 17).pointIds 17)]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M7500_7700.SplitData.node0002 := by
  change Tree.branch (106 : Fin 173) _ = Tree.branch (106 : Fin 173) _
  apply congrArg (Tree.branch (106 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0003
  · rfl
  · rfl
  · rfl

def B0001 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), (.leaf 2 (Common.fact 8).pointIds 8), (.leaf 3 (Common.fact 9).pointIds 9), (.leaf 4 (Common.fact 10).pointIds 10), (.leaf 5 (Common.fact 11).pointIds 11), B0002]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M7500_7700.SplitData.node0001 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0002

def B0000 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M7500_7700.SplitData.node0000 := by
  change Tree.branch (110 : Fin 173) _ = Tree.branch (110 : Fin 173) _
  apply congrArg (Tree.branch (110 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0001

theorem accepted0000 : B0000.accepted = true := by decide +kernel
theorem checked0000 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M7500_7700.SplitTree.Run0026
