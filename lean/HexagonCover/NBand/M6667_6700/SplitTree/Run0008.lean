import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0007
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0008
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0654 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0654 : B0654.tree = HexagonCover.NBand.M6667_6700.SplitData.node0654 := by
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

def B0653 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0654]
theorem treeEq0653 : B0653.tree = HexagonCover.NBand.M6667_6700.SplitData.node0653 := by
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
  · exact treeEq0654

def B0656 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq0656 : B0656.tree = HexagonCover.NBand.M6667_6700.SplitData.node0656 := by
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

def B0655 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0656, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0655 : B0655.tree = HexagonCover.NBand.M6667_6700.SplitData.node0655 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0656
  · rfl
  · rfl

def B0652 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0653, (.leaf 5 (Common.fact 439).pointIds 439), B0655]
theorem treeEq0652 : B0652.tree = HexagonCover.NBand.M6667_6700.SplitData.node0652 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0653
  · rfl
  · exact treeEq0655

def B0658 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0658 : B0658.tree = HexagonCover.NBand.M6667_6700.SplitData.node0658 := by
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

def B0657 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0658]
theorem treeEq0657 : B0657.tree = HexagonCover.NBand.M6667_6700.SplitData.node0657 := by
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
  · exact treeEq0658

def B0651 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0652, B0657, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0651 : B0651.tree = HexagonCover.NBand.M6667_6700.SplitData.node0651 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0652
  · exact treeEq0657
  · rfl
  · rfl

def B0661 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0661 : B0661.tree = HexagonCover.NBand.M6667_6700.SplitData.node0661 := by
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

def B0660 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0661]
theorem treeEq0660 : B0660.tree = HexagonCover.NBand.M6667_6700.SplitData.node0660 := by
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
  · exact treeEq0661

def B0659 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0660, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0659 : B0659.tree = HexagonCover.NBand.M6667_6700.SplitData.node0659 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0660
  · rfl
  · rfl

def B0650 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0651, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0659, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0650 : B0650.tree = HexagonCover.NBand.M6667_6700.SplitData.node0650 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0651
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0659
  · rfl

def B0664 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0664 : B0664.tree = HexagonCover.NBand.M6667_6700.SplitData.node0664 := by
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

def B0663 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0664]
theorem treeEq0663 : B0663.tree = HexagonCover.NBand.M6667_6700.SplitData.node0663 := by
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
  · exact treeEq0664

def B0662 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0663, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0662 : B0662.tree = HexagonCover.NBand.M6667_6700.SplitData.node0662 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0663
  · rfl
  · rfl

def B0649 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0650, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0662]
theorem treeEq0649 : B0649.tree = HexagonCover.NBand.M6667_6700.SplitData.node0649 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0650
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0662

theorem accepted0649 : B0649.accepted = true := by decide +kernel
theorem checked0649 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0649 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000]) := by
  rw [← treeEq0649]
  exact B0649.sound accepted0649
#print axioms checked0649

def Tip0615_0616 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0616 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] HexagonCover.NBand.M6667_6700.SplitTree.Run0007.checked0616
def B0637 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0637 : B0637.tree = HexagonCover.NBand.M6667_6700.SplitData.node0637 := by
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

def B0636 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0637]
theorem treeEq0636 : B0636.tree = HexagonCover.NBand.M6667_6700.SplitData.node0636 := by
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
  · exact treeEq0637

def B0639 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq0639 : B0639.tree = HexagonCover.NBand.M6667_6700.SplitData.node0639 := by
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

def B0638 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0639, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0638 : B0638.tree = HexagonCover.NBand.M6667_6700.SplitData.node0638 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0639
  · rfl
  · rfl

def B0635 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0636, (.leaf 5 (Common.fact 439).pointIds 439), B0638]
theorem treeEq0635 : B0635.tree = HexagonCover.NBand.M6667_6700.SplitData.node0635 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0636
  · rfl
  · exact treeEq0638

def B0641 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0641 : B0641.tree = HexagonCover.NBand.M6667_6700.SplitData.node0641 := by
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

def B0640 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0641]
theorem treeEq0640 : B0640.tree = HexagonCover.NBand.M6667_6700.SplitData.node0640 := by
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
  · exact treeEq0641

def B0634 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0635, B0640, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0634 : B0634.tree = HexagonCover.NBand.M6667_6700.SplitData.node0634 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0635
  · exact treeEq0640
  · rfl
  · rfl

def B0644 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0644 : B0644.tree = HexagonCover.NBand.M6667_6700.SplitData.node0644 := by
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

def B0643 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0644]
theorem treeEq0643 : B0643.tree = HexagonCover.NBand.M6667_6700.SplitData.node0643 := by
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
  · exact treeEq0644

def B0642 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0643, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0642 : B0642.tree = HexagonCover.NBand.M6667_6700.SplitData.node0642 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0643
  · rfl
  · rfl

def B0633 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0634, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0642, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0633 : B0633.tree = HexagonCover.NBand.M6667_6700.SplitData.node0633 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0634
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0642
  · rfl

def B0647 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0647 : B0647.tree = HexagonCover.NBand.M6667_6700.SplitData.node0647 := by
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

def B0646 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0647]
theorem treeEq0646 : B0646.tree = HexagonCover.NBand.M6667_6700.SplitData.node0646 := by
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
  · exact treeEq0647

def B0645 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0646, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0645 : B0645.tree = HexagonCover.NBand.M6667_6700.SplitData.node0645 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0646
  · rfl
  · rfl

def B0632 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0633, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0645]
theorem treeEq0632 : B0632.tree = HexagonCover.NBand.M6667_6700.SplitData.node0632 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0633
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0645

def B0615 : Block := .branch 74 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip0615_0616, B0632, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0615 : B0615.tree = HexagonCover.NBand.M6667_6700.SplitData.node0615 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0632
  · rfl
  · rfl
  · rfl

theorem accepted0615 : B0615.accepted = true := by decide +kernel
theorem checked0615 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0615 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152]) := by
  rw [← treeEq0615]
  exact B0615.sound accepted0615
#print axioms checked0615

def B0688 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0688 : B0688.tree = HexagonCover.NBand.M6667_6700.SplitData.node0688 := by
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

def B0687 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0688]
theorem treeEq0687 : B0687.tree = HexagonCover.NBand.M6667_6700.SplitData.node0687 := by
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
  · exact treeEq0688

def B0690 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq0690 : B0690.tree = HexagonCover.NBand.M6667_6700.SplitData.node0690 := by
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

def B0689 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0690, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0689 : B0689.tree = HexagonCover.NBand.M6667_6700.SplitData.node0689 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0690
  · rfl
  · rfl

def B0686 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0687, (.leaf 5 (Common.fact 439).pointIds 439), B0689]
theorem treeEq0686 : B0686.tree = HexagonCover.NBand.M6667_6700.SplitData.node0686 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0687
  · rfl
  · exact treeEq0689

def B0692 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0692 : B0692.tree = HexagonCover.NBand.M6667_6700.SplitData.node0692 := by
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

def B0691 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0692]
theorem treeEq0691 : B0691.tree = HexagonCover.NBand.M6667_6700.SplitData.node0691 := by
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
  · exact treeEq0692

def B0685 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0686, B0691, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0685 : B0685.tree = HexagonCover.NBand.M6667_6700.SplitData.node0685 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0686
  · exact treeEq0691
  · rfl
  · rfl

def B0695 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0695 : B0695.tree = HexagonCover.NBand.M6667_6700.SplitData.node0695 := by
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

def B0694 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0695]
theorem treeEq0694 : B0694.tree = HexagonCover.NBand.M6667_6700.SplitData.node0694 := by
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
  · exact treeEq0695

def B0693 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0694, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0693 : B0693.tree = HexagonCover.NBand.M6667_6700.SplitData.node0693 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0694
  · rfl
  · rfl

def B0684 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0685, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0693, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0684 : B0684.tree = HexagonCover.NBand.M6667_6700.SplitData.node0684 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0685
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0693
  · rfl

def B0698 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0698 : B0698.tree = HexagonCover.NBand.M6667_6700.SplitData.node0698 := by
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

def B0697 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0698]
theorem treeEq0697 : B0697.tree = HexagonCover.NBand.M6667_6700.SplitData.node0697 := by
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
  · exact treeEq0698

def B0696 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0697, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0696 : B0696.tree = HexagonCover.NBand.M6667_6700.SplitData.node0696 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0697
  · rfl
  · rfl

def B0683 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0684, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0696]
theorem treeEq0683 : B0683.tree = HexagonCover.NBand.M6667_6700.SplitData.node0683 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0684
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0696

theorem accepted0683 : B0683.accepted = true := by decide +kernel
theorem checked0683 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0683 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000]) := by
  rw [← treeEq0683]
  exact B0683.sound accepted0683
#print axioms checked0683

def B0721 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0721 : B0721.tree = HexagonCover.NBand.M6667_6700.SplitData.node0721 := by
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

def B0720 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0721]
theorem treeEq0720 : B0720.tree = HexagonCover.NBand.M6667_6700.SplitData.node0720 := by
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
  · exact treeEq0721

def B0723 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq0723 : B0723.tree = HexagonCover.NBand.M6667_6700.SplitData.node0723 := by
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

def B0722 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0723, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0722 : B0722.tree = HexagonCover.NBand.M6667_6700.SplitData.node0722 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0723
  · rfl
  · rfl

def B0719 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0720, (.leaf 5 (Common.fact 439).pointIds 439), B0722]
theorem treeEq0719 : B0719.tree = HexagonCover.NBand.M6667_6700.SplitData.node0719 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0720
  · rfl
  · exact treeEq0722

def B0725 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq0725 : B0725.tree = HexagonCover.NBand.M6667_6700.SplitData.node0725 := by
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

def B0724 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0725]
theorem treeEq0724 : B0724.tree = HexagonCover.NBand.M6667_6700.SplitData.node0724 := by
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
  · exact treeEq0725

def B0718 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0719, B0724, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0718 : B0718.tree = HexagonCover.NBand.M6667_6700.SplitData.node0718 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0719
  · exact treeEq0724
  · rfl
  · rfl

def B0728 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq0728 : B0728.tree = HexagonCover.NBand.M6667_6700.SplitData.node0728 := by
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

def B0727 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0728]
theorem treeEq0727 : B0727.tree = HexagonCover.NBand.M6667_6700.SplitData.node0727 := by
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
  · exact treeEq0728

def B0726 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0727, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0726 : B0726.tree = HexagonCover.NBand.M6667_6700.SplitData.node0726 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0727
  · rfl
  · rfl

def B0717 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0718, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0726, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0717 : B0717.tree = HexagonCover.NBand.M6667_6700.SplitData.node0717 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0718
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0726
  · rfl

def B0731 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0731 : B0731.tree = HexagonCover.NBand.M6667_6700.SplitData.node0731 := by
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

def B0730 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0731]
theorem treeEq0730 : B0730.tree = HexagonCover.NBand.M6667_6700.SplitData.node0730 := by
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
  · exact treeEq0731

def B0729 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0730, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0729 : B0729.tree = HexagonCover.NBand.M6667_6700.SplitData.node0729 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0730
  · rfl
  · rfl

def B0716 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B0717, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0729]
theorem treeEq0716 : B0716.tree = HexagonCover.NBand.M6667_6700.SplitData.node0716 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0717
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0729

theorem accepted0716 : B0716.accepted = true := by decide +kernel
theorem checked0716 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0716 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000]) := by
  rw [← treeEq0716]
  exact B0716.sound accepted0716
#print axioms checked0716

end HexagonCover.NBand.M6667_6700.SplitTree.Run0008
