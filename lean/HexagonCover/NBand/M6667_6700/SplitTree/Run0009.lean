import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0007
import HexagonCover.NBand.M6667_6700.SplitTree.Run0008
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0009
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0682_0683 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0683 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] HexagonCover.NBand.M6667_6700.SplitTree.Run0008.checked0683
def B0704 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0704 : B0704.tree = HexagonCover.NBand.M6667_6700.SplitData.node0704 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0703 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0704]
theorem treeEq0703 : B0703.tree = HexagonCover.NBand.M6667_6700.SplitData.node0703 := by
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
  · exact treeEq0704

def B0706 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq0706 : B0706.tree = HexagonCover.NBand.M6667_6700.SplitData.node0706 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0705 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0706, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0705 : B0705.tree = HexagonCover.NBand.M6667_6700.SplitData.node0705 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0706
  · rfl
  · rfl

def B0702 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0703, (.leaf 5 (Common.fact 439).pointIds 439), B0705]
theorem treeEq0702 : B0702.tree = HexagonCover.NBand.M6667_6700.SplitData.node0702 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0703
  · rfl
  · exact treeEq0705

def B0708 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0708 : B0708.tree = HexagonCover.NBand.M6667_6700.SplitData.node0708 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0707 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0708]
theorem treeEq0707 : B0707.tree = HexagonCover.NBand.M6667_6700.SplitData.node0707 := by
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
  · exact treeEq0708

def B0701 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0702, B0707, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0701 : B0701.tree = HexagonCover.NBand.M6667_6700.SplitData.node0701 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0702
  · exact treeEq0707
  · rfl
  · rfl

def B0711 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M6667_6700.SplitData.node0711 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0710 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0711]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M6667_6700.SplitData.node0710 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0711

def B0709 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0710, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0709 : B0709.tree = HexagonCover.NBand.M6667_6700.SplitData.node0709 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0710
  · rfl
  · rfl

def B0700 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0701, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0709, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0700 : B0700.tree = HexagonCover.NBand.M6667_6700.SplitData.node0700 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0701
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0709
  · rfl

def B0714 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0714 : B0714.tree = HexagonCover.NBand.M6667_6700.SplitData.node0714 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0713 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0714]
theorem treeEq0713 : B0713.tree = HexagonCover.NBand.M6667_6700.SplitData.node0713 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0714

def B0712 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0713, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M6667_6700.SplitData.node0712 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0713
  · rfl
  · rfl

def B0699 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0700, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0712]
theorem treeEq0699 : B0699.tree = HexagonCover.NBand.M6667_6700.SplitData.node0699 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0700
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0712

def B0682 : Block := .branch 74 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip0682_0683, B0699, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0682 : B0682.tree = HexagonCover.NBand.M6667_6700.SplitData.node0682 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0699
  · rfl
  · rfl
  · rfl

theorem accepted0682 : B0682.accepted = true := by decide +kernel
theorem checked0682 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0682 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152]) := by
  rw [← treeEq0682]
  exact B0682.sound accepted0682
#print axioms checked0682

def Tip0614_0649 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0649 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] HexagonCover.NBand.M6667_6700.SplitTree.Run0008.checked0649
def Tip0614_0615 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0615 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] HexagonCover.NBand.M6667_6700.SplitTree.Run0008.checked0615
def B0670 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0670 : B0670.tree = HexagonCover.NBand.M6667_6700.SplitData.node0670 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0669 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0670]
theorem treeEq0669 : B0669.tree = HexagonCover.NBand.M6667_6700.SplitData.node0669 := by
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
  · exact treeEq0670

def B0672 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq0672 : B0672.tree = HexagonCover.NBand.M6667_6700.SplitData.node0672 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0671 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0672, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0671 : B0671.tree = HexagonCover.NBand.M6667_6700.SplitData.node0671 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0672
  · rfl
  · rfl

def B0668 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0669, (.leaf 5 (Common.fact 439).pointIds 439), B0671]
theorem treeEq0668 : B0668.tree = HexagonCover.NBand.M6667_6700.SplitData.node0668 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0669
  · rfl
  · exact treeEq0671

def B0674 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0674 : B0674.tree = HexagonCover.NBand.M6667_6700.SplitData.node0674 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0673 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0674]
theorem treeEq0673 : B0673.tree = HexagonCover.NBand.M6667_6700.SplitData.node0673 := by
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
  · exact treeEq0674

def B0667 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0668, B0673, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0667 : B0667.tree = HexagonCover.NBand.M6667_6700.SplitData.node0667 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0668
  · exact treeEq0673
  · rfl
  · rfl

def B0677 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0677 : B0677.tree = HexagonCover.NBand.M6667_6700.SplitData.node0677 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0676 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0677]
theorem treeEq0676 : B0676.tree = HexagonCover.NBand.M6667_6700.SplitData.node0676 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0677

def B0675 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0676, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0675 : B0675.tree = HexagonCover.NBand.M6667_6700.SplitData.node0675 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0676
  · rfl
  · rfl

def B0666 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0667, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0675, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0666 : B0666.tree = HexagonCover.NBand.M6667_6700.SplitData.node0666 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0667
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0675
  · rfl

def B0680 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0680 : B0680.tree = HexagonCover.NBand.M6667_6700.SplitData.node0680 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0679 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0680]
theorem treeEq0679 : B0679.tree = HexagonCover.NBand.M6667_6700.SplitData.node0679 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0680

def B0678 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0679, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0678 : B0678.tree = HexagonCover.NBand.M6667_6700.SplitData.node0678 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0679
  · rfl
  · rfl

def B0665 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0666, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0678]
theorem treeEq0665 : B0665.tree = HexagonCover.NBand.M6667_6700.SplitData.node0665 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0666
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0678

def B0648 : Block := .branch 74 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip0614_0649, B0665, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0648 : B0648.tree = HexagonCover.NBand.M6667_6700.SplitData.node0648 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0665
  · rfl
  · rfl
  · rfl

def B0614 : Block := .branch 73 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip0614_0615, B0648, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq0614 : B0614.tree = HexagonCover.NBand.M6667_6700.SplitData.node0614 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0648
  · rfl
  · rfl
  · rfl

theorem accepted0614 : B0614.accepted = true := by decide +kernel
theorem checked0614 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0614 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152]) := by
  rw [← treeEq0614]
  exact B0614.sound accepted0614
#print axioms checked0614

def Tip0477_0581 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0581 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] HexagonCover.NBand.M6667_6700.SplitTree.Run0007.checked0581
def Tip0477_0547 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0547 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] HexagonCover.NBand.M6667_6700.SplitTree.Run0007.checked0547
def Tip0477_0479 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0479 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] HexagonCover.NBand.M6667_6700.SplitTree.Run0007.checked0479
def B0602 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0602 : B0602.tree = HexagonCover.NBand.M6667_6700.SplitData.node0602 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0601 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0602]
theorem treeEq0601 : B0601.tree = HexagonCover.NBand.M6667_6700.SplitData.node0601 := by
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
  · exact treeEq0602

def B0604 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq0604 : B0604.tree = HexagonCover.NBand.M6667_6700.SplitData.node0604 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0603 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0604, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0603 : B0603.tree = HexagonCover.NBand.M6667_6700.SplitData.node0603 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0604
  · rfl
  · rfl

def B0600 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0601, (.leaf 5 (Common.fact 439).pointIds 439), B0603]
theorem treeEq0600 : B0600.tree = HexagonCover.NBand.M6667_6700.SplitData.node0600 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0601
  · rfl
  · exact treeEq0603

def B0606 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0606 : B0606.tree = HexagonCover.NBand.M6667_6700.SplitData.node0606 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0605 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0606]
theorem treeEq0605 : B0605.tree = HexagonCover.NBand.M6667_6700.SplitData.node0605 := by
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
  · exact treeEq0606

def B0599 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0600, B0605, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0599 : B0599.tree = HexagonCover.NBand.M6667_6700.SplitData.node0599 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0600
  · exact treeEq0605
  · rfl
  · rfl

def B0609 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0609 : B0609.tree = HexagonCover.NBand.M6667_6700.SplitData.node0609 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0608 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0609]
theorem treeEq0608 : B0608.tree = HexagonCover.NBand.M6667_6700.SplitData.node0608 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0609

def B0607 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0608, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0607 : B0607.tree = HexagonCover.NBand.M6667_6700.SplitData.node0607 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0608
  · rfl
  · rfl

def B0598 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0599, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0607, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0598 : B0598.tree = HexagonCover.NBand.M6667_6700.SplitData.node0598 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0599
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0607
  · rfl

def B0612 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0612 : B0612.tree = HexagonCover.NBand.M6667_6700.SplitData.node0612 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0611 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0612]
theorem treeEq0611 : B0611.tree = HexagonCover.NBand.M6667_6700.SplitData.node0611 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0612

def B0610 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0611, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0610 : B0610.tree = HexagonCover.NBand.M6667_6700.SplitData.node0610 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0611
  · rfl
  · rfl

def B0597 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0598, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0610]
theorem treeEq0597 : B0597.tree = HexagonCover.NBand.M6667_6700.SplitData.node0597 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0598
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0610

def B0580 : Block := .branch 74 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip0477_0581, B0597, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq0580 : B0580.tree = HexagonCover.NBand.M6667_6700.SplitData.node0580 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0597
  · rfl
  · rfl
  · rfl

def B0546 : Block := .branch 73 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip0477_0547, B0580, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq0546 : B0546.tree = HexagonCover.NBand.M6667_6700.SplitData.node0546 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0580
  · rfl
  · rfl
  · rfl

def B0478 : Block := .branch 72 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), Tip0477_0479, B0546, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 915).pointIds 915)]
theorem treeEq0478 : B0478.tree = HexagonCover.NBand.M6667_6700.SplitData.node0478 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0546
  · rfl
  · rfl
  · rfl

def B0477 : Block := .branch 163 ![5319508136520691063723936093489332609, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B0478]
theorem treeEq0477 : B0477.tree = HexagonCover.NBand.M6667_6700.SplitData.node0477 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0478

theorem accepted0477 : B0477.accepted = true := by decide +kernel
theorem checked0477 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0477 (maskNeeds ![5319508136520691063723936093489332609, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848]) := by
  rw [← treeEq0477]
  exact B0477.sound accepted0477
#print axioms checked0477

def Tip0476_0716 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0716 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] HexagonCover.NBand.M6667_6700.SplitTree.Run0008.checked0716
def Tip0476_0682 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0682 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] checked0682
def Tip0476_0614 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0614 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] checked0614
def Tip0476_0477 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0477 ![5319508136520691063723936093489332609, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] checked0477
def B0737 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0737 : B0737.tree = HexagonCover.NBand.M6667_6700.SplitData.node0737 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0736 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0737]
theorem treeEq0736 : B0736.tree = HexagonCover.NBand.M6667_6700.SplitData.node0736 := by
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
  · exact treeEq0737

def B0739 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq0739 : B0739.tree = HexagonCover.NBand.M6667_6700.SplitData.node0739 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0738 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0739, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0738 : B0738.tree = HexagonCover.NBand.M6667_6700.SplitData.node0738 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0739
  · rfl
  · rfl

def B0735 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0736, (.leaf 5 (Common.fact 439).pointIds 439), B0738]
theorem treeEq0735 : B0735.tree = HexagonCover.NBand.M6667_6700.SplitData.node0735 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0736
  · rfl
  · exact treeEq0738

def B0741 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0741 : B0741.tree = HexagonCover.NBand.M6667_6700.SplitData.node0741 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0740 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0741]
theorem treeEq0740 : B0740.tree = HexagonCover.NBand.M6667_6700.SplitData.node0740 := by
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
  · exact treeEq0741

def B0734 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0735, B0740, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0734 : B0734.tree = HexagonCover.NBand.M6667_6700.SplitData.node0734 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0735
  · exact treeEq0740
  · rfl
  · rfl

def B0744 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0744 : B0744.tree = HexagonCover.NBand.M6667_6700.SplitData.node0744 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0743 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0744]
theorem treeEq0743 : B0743.tree = HexagonCover.NBand.M6667_6700.SplitData.node0743 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0744

def B0742 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0743, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0742 : B0742.tree = HexagonCover.NBand.M6667_6700.SplitData.node0742 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0743
  · rfl
  · rfl

def B0733 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0734, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0742, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0733 : B0733.tree = HexagonCover.NBand.M6667_6700.SplitData.node0733 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0734
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0742
  · rfl

def B0747 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0747 : B0747.tree = HexagonCover.NBand.M6667_6700.SplitData.node0747 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0746 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0747]
theorem treeEq0746 : B0746.tree = HexagonCover.NBand.M6667_6700.SplitData.node0746 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0747

def B0745 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0746, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0745 : B0745.tree = HexagonCover.NBand.M6667_6700.SplitData.node0745 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0746
  · rfl
  · rfl

def B0732 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0733, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0745]
theorem treeEq0732 : B0732.tree = HexagonCover.NBand.M6667_6700.SplitData.node0732 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0733
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0745

def B0715 : Block := .branch 74 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip0476_0716, B0732, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0715 : B0715.tree = HexagonCover.NBand.M6667_6700.SplitData.node0715 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0732
  · rfl
  · rfl
  · rfl

def B0681 : Block := .branch 73 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip0476_0682, B0715, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq0681 : B0681.tree = HexagonCover.NBand.M6667_6700.SplitData.node0681 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0715
  · rfl
  · rfl
  · rfl

def B0613 : Block := .branch 72 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), Tip0476_0614, B0681, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq0613 : B0613.tree = HexagonCover.NBand.M6667_6700.SplitData.node0613 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0681
  · rfl
  · rfl
  · rfl

def B0476 : Block := .branch 122 ![2596153381027572108707852367954305, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] ![Tip0476_0477, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B0613]
theorem treeEq0476 : B0476.tree = HexagonCover.NBand.M6667_6700.SplitData.node0476 := by
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
  · exact treeEq0613

theorem accepted0476 : B0476.accepted = true := by decide +kernel
theorem checked0476 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0476 (maskNeeds ![2596153381027572108707852367954305, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848]) := by
  rw [← treeEq0476]
  exact B0476.sound accepted0476
#print axioms checked0476

end HexagonCover.NBand.M6667_6700.SplitTree.Run0009
