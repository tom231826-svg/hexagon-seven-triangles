import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0009
import HexagonCover.NBand.M6667_6700.SplitTree.Run0010
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0011
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0784_0817 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0817 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0010.checked0817
def Tip0784_0785 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0785 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0010.checked0785
def B0836 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0836 : B0836.tree = HexagonCover.NBand.M6667_6700.SplitData.node0836 := by
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

def B0835 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0836, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0835 : B0835.tree = HexagonCover.NBand.M6667_6700.SplitData.node0835 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0836
  · rfl
  · rfl

def B0834 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0835]
theorem treeEq0834 : B0834.tree = HexagonCover.NBand.M6667_6700.SplitData.node0834 := by
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
  · exact treeEq0835

def B0839 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0839 : B0839.tree = HexagonCover.NBand.M6667_6700.SplitData.node0839 := by
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

def B0838 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0839]
theorem treeEq0838 : B0838.tree = HexagonCover.NBand.M6667_6700.SplitData.node0838 := by
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
  · exact treeEq0839

def B0837 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0838, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0837 : B0837.tree = HexagonCover.NBand.M6667_6700.SplitData.node0837 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0838
  · rfl
  · rfl

def B0833 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0834, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0837]
theorem treeEq0833 : B0833.tree = HexagonCover.NBand.M6667_6700.SplitData.node0833 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0834
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0837

def B0843 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq0843 : B0843.tree = HexagonCover.NBand.M6667_6700.SplitData.node0843 := by
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

def B0842 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0843, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq0842 : B0842.tree = HexagonCover.NBand.M6667_6700.SplitData.node0842 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0843
  · rfl
  · rfl

def B0841 : Block := .branch 158 ![10636420119660354555339164334610710913, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0842]
theorem treeEq0841 : B0841.tree = HexagonCover.NBand.M6667_6700.SplitData.node0841 := by
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
  · exact treeEq0842

def B0846 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0846 : B0846.tree = HexagonCover.NBand.M6667_6700.SplitData.node0846 := by
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

def B0845 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0846]
theorem treeEq0845 : B0845.tree = HexagonCover.NBand.M6667_6700.SplitData.node0845 := by
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
  · exact treeEq0846

def B0844 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0845, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0844 : B0844.tree = HexagonCover.NBand.M6667_6700.SplitData.node0844 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0845
  · rfl
  · rfl

def B0840 : Block := .branch 123 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B0841, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0844]
theorem treeEq0840 : B0840.tree = HexagonCover.NBand.M6667_6700.SplitData.node0840 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0841
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0844

def B0832 : Block := .branch 74 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B0833, B0840, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq0832 : B0832.tree = HexagonCover.NBand.M6667_6700.SplitData.node0832 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0833
  · exact treeEq0840
  · rfl
  · rfl
  · rfl

def B0816 : Block := .branch 73 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip0784_0817, B0832, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq0816 : B0816.tree = HexagonCover.NBand.M6667_6700.SplitData.node0816 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0832
  · rfl
  · rfl
  · rfl

def B0784 : Block := .branch 72 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), Tip0784_0785, B0816, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq0784 : B0784.tree = HexagonCover.NBand.M6667_6700.SplitData.node0784 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0816
  · rfl
  · rfl
  · rfl

theorem accepted0784 : B0784.accepted = true := by decide +kernel
theorem checked0784 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0784 (maskNeeds ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq0784]
  exact B0784.sound accepted0784
#print axioms checked0784

def B0852 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq0852 : B0852.tree = HexagonCover.NBand.M6667_6700.SplitData.node0852 := by
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

def B0851 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0852]
theorem treeEq0851 : B0851.tree = HexagonCover.NBand.M6667_6700.SplitData.node0851 := by
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
  · exact treeEq0852

def B0855 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq0855 : B0855.tree = HexagonCover.NBand.M6667_6700.SplitData.node0855 := by
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

def B0854 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0855]
theorem treeEq0854 : B0854.tree = HexagonCover.NBand.M6667_6700.SplitData.node0854 := by
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
  · exact treeEq0855

def B0853 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0854, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq0853 : B0853.tree = HexagonCover.NBand.M6667_6700.SplitData.node0853 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0854
  · rfl
  · rfl

def B0850 : Block := .branch 119 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0851, (.leaf 5 (Common.fact 419).pointIds 419), B0853]
theorem treeEq0850 : B0850.tree = HexagonCover.NBand.M6667_6700.SplitData.node0850 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0851
  · rfl
  · exact treeEq0853

def B0857 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq0857 : B0857.tree = HexagonCover.NBand.M6667_6700.SplitData.node0857 := by
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

def B0856 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0857, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq0856 : B0856.tree = HexagonCover.NBand.M6667_6700.SplitData.node0856 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0857
  · rfl
  · rfl

def B0849 : Block := .branch 112 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B0850, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B0856]
theorem treeEq0849 : B0849.tree = HexagonCover.NBand.M6667_6700.SplitData.node0849 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0850
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0856

def B0861 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq0861 : B0861.tree = HexagonCover.NBand.M6667_6700.SplitData.node0861 := by
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

def B0860 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0861]
theorem treeEq0860 : B0860.tree = HexagonCover.NBand.M6667_6700.SplitData.node0860 := by
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
  · exact treeEq0861

def B0864 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq0864 : B0864.tree = HexagonCover.NBand.M6667_6700.SplitData.node0864 := by
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

def B0863 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0864]
theorem treeEq0863 : B0863.tree = HexagonCover.NBand.M6667_6700.SplitData.node0863 := by
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
  · exact treeEq0864

def B0862 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0863, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq0862 : B0862.tree = HexagonCover.NBand.M6667_6700.SplitData.node0862 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0863
  · rfl
  · rfl

def B0859 : Block := .branch 119 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0860, (.leaf 5 (Common.fact 419).pointIds 419), B0862]
theorem treeEq0859 : B0859.tree = HexagonCover.NBand.M6667_6700.SplitData.node0859 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0860
  · rfl
  · exact treeEq0862

def B0866 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq0866 : B0866.tree = HexagonCover.NBand.M6667_6700.SplitData.node0866 := by
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

def B0865 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0866, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq0865 : B0865.tree = HexagonCover.NBand.M6667_6700.SplitData.node0865 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0866
  · rfl
  · rfl

def B0858 : Block := .branch 112 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B0859, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B0865]
theorem treeEq0858 : B0858.tree = HexagonCover.NBand.M6667_6700.SplitData.node0858 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0859
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0865

def B0848 : Block := .branch 72 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B0849, B0858, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq0848 : B0848.tree = HexagonCover.NBand.M6667_6700.SplitData.node0848 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0849
  · exact treeEq0858
  · rfl
  · rfl
  · rfl

def B0847 : Block := .branch 139 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B0848, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq0847 : B0847.tree = HexagonCover.NBand.M6667_6700.SplitData.node0847 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0848
  · rfl
  · rfl

theorem accepted0847 : B0847.accepted = true := by decide +kernel
theorem checked0847 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0847 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656]) := by
  rw [← treeEq0847]
  exact B0847.sound accepted0847
#print axioms checked0847

def Tip0768_0784 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0784 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] checked0784
def Tip0768_0847 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0847 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] checked0847
def B0771 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq0771 : B0771.tree = HexagonCover.NBand.M6667_6700.SplitData.node0771 := by
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

def B0770 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0771]
theorem treeEq0770 : B0770.tree = HexagonCover.NBand.M6667_6700.SplitData.node0770 := by
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
  · exact treeEq0771

def B0775 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq0775 : B0775.tree = HexagonCover.NBand.M6667_6700.SplitData.node0775 := by
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

def B0774 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B0775]
theorem treeEq0774 : B0774.tree = HexagonCover.NBand.M6667_6700.SplitData.node0774 := by
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
  · exact treeEq0775

def B0778 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq0778 : B0778.tree = HexagonCover.NBand.M6667_6700.SplitData.node0778 := by
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

def B0777 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B0778]
theorem treeEq0777 : B0777.tree = HexagonCover.NBand.M6667_6700.SplitData.node0777 := by
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
  · exact treeEq0778

def B0783 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq0783 : B0783.tree = HexagonCover.NBand.M6667_6700.SplitData.node0783 := by
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

def B0782 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0783, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq0782 : B0782.tree = HexagonCover.NBand.M6667_6700.SplitData.node0782 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0783
  · rfl
  · rfl

def B0781 : Block := .branch 158 ![5319508136520691063723936093489332609, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B0782]
theorem treeEq0781 : B0781.tree = HexagonCover.NBand.M6667_6700.SplitData.node0781 := by
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
  · exact treeEq0782

def B0780 : Block := .branch 163 ![5319508136520691063723936093489332609, 618970757512454185343256066, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B0781]
theorem treeEq0780 : B0780.tree = HexagonCover.NBand.M6667_6700.SplitData.node0780 := by
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
  · exact treeEq0781

def B0779 : Block := .branch 122 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B0780, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip0768_0784]
theorem treeEq0779 : B0779.tree = HexagonCover.NBand.M6667_6700.SplitData.node0779 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0780
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0776 : Block := .branch 121 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664091495163138109364451942813045360164928] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B0777, (.leaf 5 (Common.fact 430).pointIds 430), B0779]
theorem treeEq0776 : B0776.tree = HexagonCover.NBand.M6667_6700.SplitData.node0776 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0777
  · rfl
  · exact treeEq0779

def B0773 : Block := .branch 120 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B0774, (.leaf 5 (Common.fact 163).pointIds 163), B0776]
theorem treeEq0773 : B0773.tree = HexagonCover.NBand.M6667_6700.SplitData.node0773 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0774
  · rfl
  · exact treeEq0776

def B0772 : Block := .branch 140 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0773, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq0772 : B0772.tree = HexagonCover.NBand.M6667_6700.SplitData.node0772 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0773
  · rfl
  · rfl

def B0769 : Block := .branch 119 ![2596153381027572108707852367954305, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0770, (.leaf 5 (Common.fact 419).pointIds 419), B0772]
theorem treeEq0769 : B0769.tree = HexagonCover.NBand.M6667_6700.SplitData.node0769 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0770
  · rfl
  · exact treeEq0772

def B0768 : Block := .branch 111 ![4951760158294442604203344257, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B0769, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip0768_0847]
theorem treeEq0768 : B0768.tree = HexagonCover.NBand.M6667_6700.SplitData.node0768 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0769
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0768 : B0768.accepted = true := by decide +kernel
theorem checked0768 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0768 (maskNeeds ![4951760158294442604203344257, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089501645662985649069313885610960224320]) := by
  rw [← treeEq0768]
  exact B0768.sound accepted0768
#print axioms checked0768

def Tip0460_0476 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0476 ![2596153381027572108707852367954305, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664092824391450806930381903970479816310848] HexagonCover.NBand.M6667_6700.SplitTree.Run0009.checked0476
def Tip0460_0748 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0748 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089502943103374982662106317486690926656] HexagonCover.NBand.M6667_6700.SplitTree.Run0010.checked0748
def Tip0460_0768 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0768 ![4951760158294442604203344257, 618970757512454185343256066, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664089501645662985649069313885610960224320] checked0768
def B0463 : Block := .branch 132 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764357729643384042495148096] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq0463 : B0463.tree = HexagonCover.NBand.M6667_6700.SplitData.node0463 := by
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

def B0462 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 324518553658426726783156020674576, 393248, 6360455125664089500023387130006992737320205033144384] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B0463]
theorem treeEq0462 : B0462.tree = HexagonCover.NBand.M6667_6700.SplitData.node0462 := by
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
  · exact treeEq0463

def B0468 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq0468 : B0468.tree = HexagonCover.NBand.M6667_6700.SplitData.node0468 := by
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

def B0467 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0468]
theorem treeEq0467 : B0467.tree = HexagonCover.NBand.M6667_6700.SplitData.node0467 := by
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
  · exact treeEq0468

def B0472 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq0472 : B0472.tree = HexagonCover.NBand.M6667_6700.SplitData.node0472 := by
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

def B0471 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B0472]
theorem treeEq0471 : B0471.tree = HexagonCover.NBand.M6667_6700.SplitData.node0471 := by
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
  · exact treeEq0472

def B0475 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq0475 : B0475.tree = HexagonCover.NBand.M6667_6700.SplitData.node0475 := by
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

def B0474 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B0475]
theorem treeEq0474 : B0474.tree = HexagonCover.NBand.M6667_6700.SplitData.node0474 := by
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
  · exact treeEq0475

def B0473 : Block := .branch 121 ![2596153381027572108707852367954305, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664091495163455022014509000163419535966272] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B0474, (.leaf 5 (Common.fact 430).pointIds 430), Tip0460_0476]
theorem treeEq0473 : B0473.tree = HexagonCover.NBand.M6667_6700.SplitData.node0473 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0474
  · rfl
  · rfl

def B0470 : Block := .branch 120 ![2596153381027572108707852367954305, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B0471, (.leaf 5 (Common.fact 163).pointIds 163), B0473]
theorem treeEq0470 : B0470.tree = HexagonCover.NBand.M6667_6700.SplitData.node0470 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0471
  · rfl
  · exact treeEq0473

def B0469 : Block := .branch 140 ![2596153381027572108707852367954305, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 522673715590561479879743397015195972894736, 393248, 6360455125664090165935459237098636096356359255621696] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0470, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq0469 : B0469.tree = HexagonCover.NBand.M6667_6700.SplitData.node0469 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0470
  · rfl
  · rfl

def B0466 : Block := .branch 119 ![2596153381027572108707852367954305, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0467, (.leaf 5 (Common.fact 419).pointIds 419), B0469]
theorem treeEq0466 : B0466.tree = HexagonCover.NBand.M6667_6700.SplitData.node0466 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0467
  · rfl
  · exact treeEq0469

def B0465 : Block := .branch 111 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![B0466, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip0460_0748]
theorem treeEq0465 : B0465.tree = HexagonCover.NBand.M6667_6700.SplitData.node0465 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0466
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0464 : Block := .branch 69 ![4951760158294442604203344257, 618970167216643826637604354, 2398076729582241716228, 29014219670751100192972808, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![B0465, Tip0460_0768, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq0464 : B0464.tree = HexagonCover.NBand.M6667_6700.SplitData.node0464 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0465
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0461 : Block := .branch 108 ![4951760158294442604203344257, 618970167216643826637604354, 2398076729582241716228, 29014219670751100192972808, 522673715590561479879743397015195972894736, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B0462, (.leaf 5 (Common.fact 136).pointIds 136), B0464]
theorem treeEq0461 : B0461.tree = HexagonCover.NBand.M6667_6700.SplitData.node0461 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0462
  · rfl
  · exact treeEq0464

def B0869 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240258071987486287549956160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 957).pointIds 957)]
theorem treeEq0869 : B0869.tree = HexagonCover.NBand.M6667_6700.SplitData.node0869 := by
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

def B0868 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605907335081422450087952448] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B0869]
theorem treeEq0868 : B0868.tree = HexagonCover.NBand.M6667_6700.SplitData.node0868 := by
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
  · exact treeEq0869

def B0867 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820541041988555074170257472] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0868, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq0867 : B0867.tree = HexagonCover.NBand.M6667_6700.SplitData.node0867 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0868
  · rfl
  · rfl

def B0460 : Block := .branch 101 ![4951760158294442604203344257, 618970167216643826637604354, 2398076729582241716228, 29014219670751100192972808, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![B0461, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B0867]
theorem treeEq0460 : B0460.tree = HexagonCover.NBand.M6667_6700.SplitData.node0460 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0461
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0867

theorem accepted0460 : B0460.accepted = true := by decide +kernel
theorem checked0460 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0460 (maskNeeds ![4951760158294442604203344257, 618970167216643826637604354, 2398076729582241716228, 29014219670751100192972808, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq0460]
  exact B0460.sound accepted0460
#print axioms checked0460

end HexagonCover.NBand.M6667_6700.SplitTree.Run0011
