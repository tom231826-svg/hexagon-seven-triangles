import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0010
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0753 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq0753 : B0753.tree = HexagonCover.NBand.M6667_6700.SplitData.node0753 := by
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

def B0752 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0753]
theorem treeEq0752 : B0752.tree = HexagonCover.NBand.M6667_6700.SplitData.node0752 := by
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
  · exact treeEq0753

def B0756 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq0756 : B0756.tree = HexagonCover.NBand.M6667_6700.SplitData.node0756 := by
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

def B0755 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0756]
theorem treeEq0755 : B0755.tree = HexagonCover.NBand.M6667_6700.SplitData.node0755 := by
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
  · exact treeEq0756

def B0754 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0755, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq0754 : B0754.tree = HexagonCover.NBand.M6667_6700.SplitData.node0754 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0755
  · rfl
  · rfl

def B0751 : Block := .branch 119 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0752, (.leaf 5 (Common.fact 419).pointIds 419), B0754]
theorem treeEq0751 : B0751.tree = HexagonCover.NBand.M6667_6700.SplitData.node0751 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0752
  · rfl
  · exact treeEq0754

def B0758 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq0758 : B0758.tree = HexagonCover.NBand.M6667_6700.SplitData.node0758 := by
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

def B0757 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0758, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq0757 : B0757.tree = HexagonCover.NBand.M6667_6700.SplitData.node0757 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0758
  · rfl
  · rfl

def B0750 : Block := .branch 112 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B0751, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B0757]
theorem treeEq0750 : B0750.tree = HexagonCover.NBand.M6667_6700.SplitData.node0750 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0751
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0757

def B0762 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq0762 : B0762.tree = HexagonCover.NBand.M6667_6700.SplitData.node0762 := by
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

def B0761 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0762]
theorem treeEq0761 : B0761.tree = HexagonCover.NBand.M6667_6700.SplitData.node0761 := by
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
  · exact treeEq0762

def B0765 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq0765 : B0765.tree = HexagonCover.NBand.M6667_6700.SplitData.node0765 := by
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

def B0764 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0765]
theorem treeEq0764 : B0764.tree = HexagonCover.NBand.M6667_6700.SplitData.node0764 := by
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
  · exact treeEq0765

def B0763 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0764, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq0763 : B0763.tree = HexagonCover.NBand.M6667_6700.SplitData.node0763 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0764
  · rfl
  · rfl

def B0760 : Block := .branch 119 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0761, (.leaf 5 (Common.fact 419).pointIds 419), B0763]
theorem treeEq0760 : B0760.tree = HexagonCover.NBand.M6667_6700.SplitData.node0760 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0761
  · rfl
  · exact treeEq0763

def B0767 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq0767 : B0767.tree = HexagonCover.NBand.M6667_6700.SplitData.node0767 := by
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

def B0766 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0767, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq0766 : B0766.tree = HexagonCover.NBand.M6667_6700.SplitData.node0766 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0767
  · rfl
  · rfl

def B0759 : Block := .branch 112 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B0760, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B0766]
theorem treeEq0759 : B0759.tree = HexagonCover.NBand.M6667_6700.SplitData.node0759 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0760
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0766

def B0749 : Block := .branch 72 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B0750, B0759, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq0749 : B0749.tree = HexagonCover.NBand.M6667_6700.SplitData.node0749 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0750
  · exact treeEq0759
  · rfl
  · rfl
  · rfl

def B0748 : Block := .branch 139 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B0749, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq0748 : B0748.tree = HexagonCover.NBand.M6667_6700.SplitData.node0748 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0749
  · rfl
  · rfl

theorem accepted0748 : B0748.accepted = true := by decide +kernel
theorem checked0748 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0748 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656]) := by
  rw [← treeEq0748]
  exact B0748.sound accepted0748
#print axioms checked0748

def B0790 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0790 : B0790.tree = HexagonCover.NBand.M6667_6700.SplitData.node0790 := by
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

def B0789 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0790, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0789 : B0789.tree = HexagonCover.NBand.M6667_6700.SplitData.node0789 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0790
  · rfl
  · rfl

def B0788 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0789]
theorem treeEq0788 : B0788.tree = HexagonCover.NBand.M6667_6700.SplitData.node0788 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0789

def B0793 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0793 : B0793.tree = HexagonCover.NBand.M6667_6700.SplitData.node0793 := by
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

def B0792 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0793]
theorem treeEq0792 : B0792.tree = HexagonCover.NBand.M6667_6700.SplitData.node0792 := by
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
  · exact treeEq0793

def B0791 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0792, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0791 : B0791.tree = HexagonCover.NBand.M6667_6700.SplitData.node0791 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0792
  · rfl
  · rfl

def B0787 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0788, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0791]
theorem treeEq0787 : B0787.tree = HexagonCover.NBand.M6667_6700.SplitData.node0787 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0788
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0791

def B0797 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0797 : B0797.tree = HexagonCover.NBand.M6667_6700.SplitData.node0797 := by
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

def B0796 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0797, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0796 : B0796.tree = HexagonCover.NBand.M6667_6700.SplitData.node0796 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0797
  · rfl
  · rfl

def B0795 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0796]
theorem treeEq0795 : B0795.tree = HexagonCover.NBand.M6667_6700.SplitData.node0795 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0796

def B0800 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0800 : B0800.tree = HexagonCover.NBand.M6667_6700.SplitData.node0800 := by
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

def B0799 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0800]
theorem treeEq0799 : B0799.tree = HexagonCover.NBand.M6667_6700.SplitData.node0799 := by
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
  · exact treeEq0800

def B0798 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0799, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0798 : B0798.tree = HexagonCover.NBand.M6667_6700.SplitData.node0798 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0799
  · rfl
  · rfl

def B0794 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0795, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0798]
theorem treeEq0794 : B0794.tree = HexagonCover.NBand.M6667_6700.SplitData.node0794 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0795
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0798

def B0786 : Block := .branch 74 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B0787, B0794, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0786 : B0786.tree = HexagonCover.NBand.M6667_6700.SplitData.node0786 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0787
  · exact treeEq0794
  · rfl
  · rfl
  · rfl

theorem accepted0786 : B0786.accepted = true := by decide +kernel
theorem checked0786 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0786 (maskNeeds ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq0786]
  exact B0786.sound accepted0786
#print axioms checked0786

def B0821 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0821 : B0821.tree = HexagonCover.NBand.M6667_6700.SplitData.node0821 := by
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

def B0820 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0821, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0820 : B0820.tree = HexagonCover.NBand.M6667_6700.SplitData.node0820 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0821
  · rfl
  · rfl

def B0819 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0820]
theorem treeEq0819 : B0819.tree = HexagonCover.NBand.M6667_6700.SplitData.node0819 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0820

def B0824 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0824 : B0824.tree = HexagonCover.NBand.M6667_6700.SplitData.node0824 := by
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

def B0823 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0824]
theorem treeEq0823 : B0823.tree = HexagonCover.NBand.M6667_6700.SplitData.node0823 := by
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
  · exact treeEq0824

def B0822 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0823, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0822 : B0822.tree = HexagonCover.NBand.M6667_6700.SplitData.node0822 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0823
  · rfl
  · rfl

def B0818 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0819, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0822]
theorem treeEq0818 : B0818.tree = HexagonCover.NBand.M6667_6700.SplitData.node0818 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0819
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0822

def B0828 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0828 : B0828.tree = HexagonCover.NBand.M6667_6700.SplitData.node0828 := by
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

def B0827 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0828, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0827 : B0827.tree = HexagonCover.NBand.M6667_6700.SplitData.node0827 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0828
  · rfl
  · rfl

def B0826 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0827]
theorem treeEq0826 : B0826.tree = HexagonCover.NBand.M6667_6700.SplitData.node0826 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0827

def B0831 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0831 : B0831.tree = HexagonCover.NBand.M6667_6700.SplitData.node0831 := by
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

def B0830 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0831]
theorem treeEq0830 : B0830.tree = HexagonCover.NBand.M6667_6700.SplitData.node0830 := by
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
  · exact treeEq0831

def B0829 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0830, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0829 : B0829.tree = HexagonCover.NBand.M6667_6700.SplitData.node0829 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0830
  · rfl
  · rfl

def B0825 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0826, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0829]
theorem treeEq0825 : B0825.tree = HexagonCover.NBand.M6667_6700.SplitData.node0825 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0826
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0829

def B0817 : Block := .branch 74 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B0818, B0825, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0817 : B0817.tree = HexagonCover.NBand.M6667_6700.SplitData.node0817 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0818
  · exact treeEq0825
  · rfl
  · rfl
  · rfl

theorem accepted0817 : B0817.accepted = true := by decide +kernel
theorem checked0817 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0817 (maskNeeds ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq0817]
  exact B0817.sound accepted0817
#print axioms checked0817

def Tip0785_0786 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0786 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] checked0786
def B0805 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0805 : B0805.tree = HexagonCover.NBand.M6667_6700.SplitData.node0805 := by
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

def B0804 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0805, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0804 : B0804.tree = HexagonCover.NBand.M6667_6700.SplitData.node0804 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0805
  · rfl
  · rfl

def B0803 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0804]
theorem treeEq0803 : B0803.tree = HexagonCover.NBand.M6667_6700.SplitData.node0803 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0804

def B0808 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0808 : B0808.tree = HexagonCover.NBand.M6667_6700.SplitData.node0808 := by
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

def B0807 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0808]
theorem treeEq0807 : B0807.tree = HexagonCover.NBand.M6667_6700.SplitData.node0807 := by
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
  · exact treeEq0808

def B0806 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0807, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0806 : B0806.tree = HexagonCover.NBand.M6667_6700.SplitData.node0806 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0807
  · rfl
  · rfl

def B0802 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0803, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0806]
theorem treeEq0802 : B0802.tree = HexagonCover.NBand.M6667_6700.SplitData.node0802 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0803
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0806

def B0812 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0812 : B0812.tree = HexagonCover.NBand.M6667_6700.SplitData.node0812 := by
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

def B0811 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0812, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0811 : B0811.tree = HexagonCover.NBand.M6667_6700.SplitData.node0811 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0812
  · rfl
  · rfl

def B0810 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0811]
theorem treeEq0810 : B0810.tree = HexagonCover.NBand.M6667_6700.SplitData.node0810 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0811

def B0815 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0815 : B0815.tree = HexagonCover.NBand.M6667_6700.SplitData.node0815 := by
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

def B0814 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0815]
theorem treeEq0814 : B0814.tree = HexagonCover.NBand.M6667_6700.SplitData.node0814 := by
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
  · exact treeEq0815

def B0813 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0814, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0813 : B0813.tree = HexagonCover.NBand.M6667_6700.SplitData.node0813 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0814
  · rfl
  · rfl

def B0809 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0810, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0813]
theorem treeEq0809 : B0809.tree = HexagonCover.NBand.M6667_6700.SplitData.node0809 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0810
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0813

def B0801 : Block := .branch 74 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B0802, B0809, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0801 : B0801.tree = HexagonCover.NBand.M6667_6700.SplitData.node0801 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0802
  · exact treeEq0809
  · rfl
  · rfl
  · rfl

def B0785 : Block := .branch 73 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip0785_0786, B0801, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq0785 : B0785.tree = HexagonCover.NBand.M6667_6700.SplitData.node0785 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0801
  · rfl
  · rfl
  · rfl

theorem accepted0785 : B0785.accepted = true := by decide +kernel
theorem checked0785 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0785 (maskNeeds ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq0785]
  exact B0785.sound accepted0785
#print axioms checked0785

end HexagonCover.NBand.M6667_6700.SplitTree.Run0010
