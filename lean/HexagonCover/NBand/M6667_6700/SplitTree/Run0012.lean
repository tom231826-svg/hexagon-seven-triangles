import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0011
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0012
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0454_0460 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0460 ![4951760158294442604203344257, 618970167216643826637604354, 2398076729582241716228, 29014219670751100192972808, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] HexagonCover.NBand.M6667_6700.SplitTree.Run0011.checked0460
def B0872 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180749340131798850933144245764160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq0872 : B0872.tree = HexagonCover.NBand.M6667_6700.SplitData.node0872 := by
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

def B0871 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060462705781061944869306783760448] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B0872]
theorem treeEq0871 : B0871.tree = HexagonCover.NBand.M6667_6700.SplitData.node0871 := by
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
  · exact treeEq0872

def B0870 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358536920414768852001930866065472] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0871, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 958).pointIds 958)]
theorem treeEq0870 : B0870.tree = HexagonCover.NBand.M6667_6700.SplitData.node0870 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0871
  · rfl
  · rfl

def B0459 : Block := .branch 91 ![4951760158294442604203344257, 618970167216643826637604354, 2398076729582241716228, 29014219670751100192972808, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![Tip0454_0460, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B0870]
theorem treeEq0459 : B0459.tree = HexagonCover.NBand.M6667_6700.SplitData.node0459 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0870

def B0875 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040558027635171373431593107520] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq0875 : B0875.tree = HexagonCover.NBand.M6667_6700.SplitData.node0875 := by
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

def B0874 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923676898265309594131103808] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B0875]
theorem treeEq0874 : B0874.tree = HexagonCover.NBand.M6667_6700.SplitData.node0874 := by
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
  · exact treeEq0875

def B0873 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138310605172442218213408832] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0874, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq0873 : B0873.tree = HexagonCover.NBand.M6667_6700.SplitData.node0873 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0874
  · rfl
  · rfl

def B0458 : Block := .branch 89 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 117).pointIds 117), B0459, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B0873]
theorem treeEq0458 : B0458.tree = HexagonCover.NBand.M6667_6700.SplitData.node0458 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0459
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0873

def B0878 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929078925041369935500542016] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq0878 : B0878.tree = HexagonCover.NBand.M6667_6700.SplitData.node0878 := by
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

def B0877 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294728188135306098038538304] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B0878]
theorem treeEq0877 : B0877.tree = HexagonCover.NBand.M6667_6700.SplitData.node0877 := by
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
  · exact treeEq0878

def B0876 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461422011952099789096296644672] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0877, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq0876 : B0876.tree = HexagonCover.NBand.M6667_6700.SplitData.node0876 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0877
  · rfl
  · rfl

def B0457 : Block := .branch 86 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B0458, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B0876]
theorem treeEq0457 : B0457.tree = HexagonCover.NBand.M6667_6700.SplitData.node0457 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0458
  · rfl
  · rfl
  · exact treeEq0876

def B0881 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6734599544820800647083213573217930360669883178942528] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 965).pointIds 965)]
theorem treeEq0881 : B0881.tree = HexagonCover.NBand.M6667_6700.SplitData.node0881 := by
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

def B0880 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 2993155710065612352971116801974439986629133943799824, 393248, 5986310706507378352962926938867193454606045716938816] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B0881]
theorem treeEq0880 : B0880.tree = HexagonCover.NBand.M6667_6700.SplitData.node0880 := by
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
  · exact treeEq0881

def B0879 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 5986310706507378354261001153500900361738669799243840] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0880, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq0879 : B0879.tree = HexagonCover.NBand.M6667_6700.SplitData.node0879 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0880
  · rfl
  · rfl

def B0456 : Block := .branch 85 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B0457, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B0879]
theorem treeEq0456 : B0456.tree = HexagonCover.NBand.M6667_6700.SplitData.node0456 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0457
  · rfl
  · rfl
  · exact treeEq0879

def B0455 : Block := .branch 137 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B0456, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 898).pointIds 898)]
theorem treeEq0455 : B0455.tree = HexagonCover.NBand.M6667_6700.SplitData.node0455 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0456
  · rfl
  · rfl

def B0454 : Block := .branch 138 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B0455, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 897).pointIds 897)]
theorem treeEq0454 : B0454.tree = HexagonCover.NBand.M6667_6700.SplitData.node0454 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0455
  · rfl
  · rfl

theorem accepted0454 : B0454.accepted = true := by decide +kernel
theorem checked0454 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0454 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq0454]
  exact B0454.sound accepted0454
#print axioms checked0454

def B0893 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864553951735076251741192256] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq0893 : B0893.tree = HexagonCover.NBand.M6667_6700.SplitData.node0893 := by
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

def B0892 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230203214829012414279188544] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B0893]
theorem treeEq0892 : B0892.tree = HexagonCover.NBand.M6667_6700.SplitData.node0892 := by
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
  · exact treeEq0893

def B0891 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444836921736145038361493568] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0892, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq0891 : B0891.tree = HexagonCover.NBand.M6667_6700.SplitData.node0891 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0892
  · rfl
  · rfl

def B0896 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 1298074234354309339596812249989184] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq0896 : B0896.tree = HexagonCover.NBand.M6667_6700.SplitData.node0896 := by
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

def B0895 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168289479848964679853508395072] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0896, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0895 : B0895.tree = HexagonCover.NBand.M6667_6700.SplitData.node0895 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0896
  · rfl
  · rfl

def B0894 : Block := .branch 170 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168289479848964679853508395072] ![(.leaf 0 (Common.fact 872).pointIds 872), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 967).pointIds 967), (.leaf 4 (Common.fact 875).pointIds 875), B0895, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq0894 : B0894.tree = HexagonCover.NBand.M6667_6700.SplitData.node0894 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0895
  · rfl

def B0890 : Block := .branch 84 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168270137035850845786713096256] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B0891, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B0894]
theorem treeEq0890 : B0890.tree = HexagonCover.NBand.M6667_6700.SplitData.node0890 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0891
  · rfl
  · rfl
  · exact treeEq0894

def B0899 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq0899 : B0899.tree = HexagonCover.NBand.M6667_6700.SplitData.node0899 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0898 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168271043730215556758594125888] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0899, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0898 : B0898.tree = HexagonCover.NBand.M6667_6700.SplitData.node0898 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0899
  · rfl
  · rfl

def B0897 : Block := .branch 170 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168271043730215556758594125888] ![(.leaf 0 (Common.fact 872).pointIds 872), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 967).pointIds 967), (.leaf 4 (Common.fact 875).pointIds 875), B0898, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq0897 : B0897.tree = HexagonCover.NBand.M6667_6700.SplitData.node0897 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0898
  · rfl

def B0889 : Block := .branch 80 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168270137035850845786713096256] ![B0890, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B0897]
theorem treeEq0889 : B0889.tree = HexagonCover.NBand.M6667_6700.SplitData.node0889 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0890
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0897

def B0888 : Block := .branch 95 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168270137035850845786713096256] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), B0889, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq0888 : B0888.tree = HexagonCover.NBand.M6667_6700.SplitData.node0888 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0889
  · rfl
  · rfl
  · rfl

theorem accepted0888 : B0888.accepted = true := by decide +kernel
theorem checked0888 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0888 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168270137035850845786713096256]) := by
  rw [← treeEq0888]
  exact B0888.sound accepted0888
#print axioms checked0888

def Tip0444_0454 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0454 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] checked0454
def Tip0444_0888 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0888 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168270137035850845786713096256] checked0888
def B0884 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261001134158087247904603003945024] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq0884 : B0884.tree = HexagonCover.NBand.M6667_6700.SplitData.node0884 := by
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

def B0883 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0884, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0883 : B0883.tree = HexagonCover.NBand.M6667_6700.SplitData.node0883 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0884
  · rfl
  · rfl

def B0882 : Block := .branch 170 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 872).pointIds 872), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 967).pointIds 967), (.leaf 4 (Common.fact 875).pointIds 875), B0883, (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq0882 : B0882.tree = HexagonCover.NBand.M6667_6700.SplitData.node0882 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0883
  · rfl

def B0453 : Block := .branch 84 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), Tip0444_0454, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B0882]
theorem treeEq0453 : B0453.tree = HexagonCover.NBand.M6667_6700.SplitData.node0453 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0882

def B0887 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq0887 : B0887.tree = HexagonCover.NBand.M6667_6700.SplitData.node0887 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0886 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168271043730215556758594125888] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0887, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0886 : B0886.tree = HexagonCover.NBand.M6667_6700.SplitData.node0886 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0887
  · rfl
  · rfl

def B0885 : Block := .branch 170 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168271043730215556758594125888] ![(.leaf 0 (Common.fact 872).pointIds 872), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 967).pointIds 967), (.leaf 4 (Common.fact 875).pointIds 875), B0886, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq0885 : B0885.tree = HexagonCover.NBand.M6667_6700.SplitData.node0885 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0886
  · rfl

def B0452 : Block := .branch 80 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![B0453, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B0885]
theorem treeEq0452 : B0452.tree = HexagonCover.NBand.M6667_6700.SplitData.node0452 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0453
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0885

def B0451 : Block := .branch 78 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 87).pointIds 87), B0452, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip0444_0888]
theorem treeEq0451 : B0451.tree = HexagonCover.NBand.M6667_6700.SplitData.node0451 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0452
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0450 : Block := .branch 172 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168269834804395942129419419712] ![(.leaf 0 (Common.fact 891).pointIds 891), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 895).pointIds 895), (.leaf 5 (Common.fact 896).pointIds 896), B0451]
theorem treeEq0450 : B0450.tree = HexagonCover.NBand.M6667_6700.SplitData.node0450 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0451

def B0449 : Block := .branch 134 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168269834804395942129419419712] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B0450, (.leaf 6 (Common.fact 890).pointIds 890)]
theorem treeEq0449 : B0449.tree = HexagonCover.NBand.M6667_6700.SplitData.node0449 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0450
  · rfl

def B0448 : Block := .branch 143 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 374144419156711148359168269834804395942129419419712] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B0449, (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq0448 : B0448.tree = HexagonCover.NBand.M6667_6700.SplitData.node0448 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0449
  · rfl

def B0447 : Block := .branch 168 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 1299024952659435942910210688417856] ![(.leaf 0 (Common.fact 859).pointIds 859), (.leaf 1 (Common.fact 860).pointIds 860), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 888).pointIds 888), (.leaf 4 (Common.fact 862).pointIds 862), (.leaf 5 (Common.fact 318).pointIds 318), B0448]
theorem treeEq0447 : B0447.tree = HexagonCover.NBand.M6667_6700.SplitData.node0447 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0448

def B0446 : Block := .branch 83 ![4951760158294442604203344257, 147573953689188042242, 2416523473655951267844, 24584, 356811923176489970264571492362373784095784976, 393248, 1299024952659435942910210688417856] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 99).pointIds 99), B0447, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq0446 : B0446.tree = HexagonCover.NBand.M6667_6700.SplitData.node0446 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0447
  · rfl
  · rfl
  · rfl

def B0445 : Block := .branch 92 ![1152921504606847361, 147573953689188042242, 2416523473655951267844, 24584, 356811923176489970264571492362373784095784976, 393248, 1299024952659435942910210688417856] ![B0446, (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 835).pointIds 835), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq0445 : B0445.tree = HexagonCover.NBand.M6667_6700.SplitData.node0445 := by
  change Tree.branch (92 : Fin 173) _ = Tree.branch (92 : Fin 173) _
  apply congrArg (Tree.branch (92 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0446
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0444 : Block := .branch 148 ![1152921504606847361, 147573953689188042242, 2416523473655951267844, 24584, 98320, 393248, 1299024952659435942910210688417856] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B0445, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 884).pointIds 884)]
theorem treeEq0444 : B0444.tree = HexagonCover.NBand.M6667_6700.SplitData.node0444 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0445
  · rfl
  · rfl

theorem accepted0444 : B0444.accepted = true := by decide +kernel
theorem checked0444 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0444 (maskNeeds ![1152921504606847361, 147573953689188042242, 2416523473655951267844, 24584, 98320, 393248, 1299024952659435942910210688417856]) := by
  rw [← treeEq0444]
  exact B0444.sound accepted0444
#print axioms checked0444

def B0977 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq0977 : B0977.tree = HexagonCover.NBand.M6667_6700.SplitData.node0977 := by
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

def B0976 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0977]
theorem treeEq0976 : B0976.tree = HexagonCover.NBand.M6667_6700.SplitData.node0976 := by
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
  · exact treeEq0977

def B0979 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq0979 : B0979.tree = HexagonCover.NBand.M6667_6700.SplitData.node0979 := by
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

def B0978 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B0979, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq0978 : B0978.tree = HexagonCover.NBand.M6667_6700.SplitData.node0978 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0979
  · rfl
  · rfl

def B0975 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B0976, (.leaf 5 (Common.fact 439).pointIds 439), B0978]
theorem treeEq0975 : B0975.tree = HexagonCover.NBand.M6667_6700.SplitData.node0975 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0976
  · rfl
  · exact treeEq0978

def B0981 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq0981 : B0981.tree = HexagonCover.NBand.M6667_6700.SplitData.node0981 := by
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

def B0980 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0981]
theorem treeEq0980 : B0980.tree = HexagonCover.NBand.M6667_6700.SplitData.node0980 := by
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
  · exact treeEq0981

def B0974 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715684808496787692392546368] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0975, B0980, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq0974 : B0974.tree = HexagonCover.NBand.M6667_6700.SplitData.node0974 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0975
  · exact treeEq0980
  · rfl
  · rfl

def B0984 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233346055704656513842282560] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq0984 : B0984.tree = HexagonCover.NBand.M6667_6700.SplitData.node0984 := by
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

def B0983 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699695943108080401163994267712] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0984]
theorem treeEq0983 : B0983.tree = HexagonCover.NBand.M6667_6700.SplitData.node0983 := by
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
  · exact treeEq0984

def B0982 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724991292464235241714316944097148992] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B0983, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq0982 : B0982.tree = HexagonCover.NBand.M6667_6700.SplitData.node0982 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0983
  · rfl
  · rfl

def B0973 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B0974, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0982, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq0973 : B0973.tree = HexagonCover.NBand.M6667_6700.SplitData.node0973 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0974
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0982
  · rfl

def B0987 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0987 : B0987.tree = HexagonCover.NBand.M6667_6700.SplitData.node0987 := by
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

def B0986 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0987]
theorem treeEq0986 : B0986.tree = HexagonCover.NBand.M6667_6700.SplitData.node0986 := by
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
  · exact treeEq0987

def B0985 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B0986, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0985 : B0985.tree = HexagonCover.NBand.M6667_6700.SplitData.node0985 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0986
  · rfl
  · rfl

def B0972 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B0973, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0985]
theorem treeEq0972 : B0972.tree = HexagonCover.NBand.M6667_6700.SplitData.node0972 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0973
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0985

theorem accepted0972 : B0972.accepted = true := by decide +kernel
theorem checked0972 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0972 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624]) := by
  rw [← treeEq0972]
  exact B0972.sound accepted0972
#print axioms checked0972

def Tip0971_0972 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0972 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] checked0972
def B0993 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq0993 : B0993.tree = HexagonCover.NBand.M6667_6700.SplitData.node0993 := by
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

def B0992 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0993]
theorem treeEq0992 : B0992.tree = HexagonCover.NBand.M6667_6700.SplitData.node0992 := by
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
  · exact treeEq0993

def B0995 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq0995 : B0995.tree = HexagonCover.NBand.M6667_6700.SplitData.node0995 := by
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

def B0994 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B0995, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq0994 : B0994.tree = HexagonCover.NBand.M6667_6700.SplitData.node0994 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0995
  · rfl
  · rfl

def B0991 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B0992, (.leaf 5 (Common.fact 439).pointIds 439), B0994]
theorem treeEq0991 : B0991.tree = HexagonCover.NBand.M6667_6700.SplitData.node0991 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0992
  · rfl
  · exact treeEq0994

def B0997 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq0997 : B0997.tree = HexagonCover.NBand.M6667_6700.SplitData.node0997 := by
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

def B0996 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0997]
theorem treeEq0996 : B0996.tree = HexagonCover.NBand.M6667_6700.SplitData.node0996 := by
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
  · exact treeEq0997

def B0990 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715684808496787692392546368] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0991, B0996, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq0990 : B0990.tree = HexagonCover.NBand.M6667_6700.SplitData.node0990 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0991
  · exact treeEq0996
  · rfl
  · rfl

def B1000 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233346055704656513842282560] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq1000 : B1000.tree = HexagonCover.NBand.M6667_6700.SplitData.node1000 := by
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

def B0999 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699695943108080401163994267712] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1000]
theorem treeEq0999 : B0999.tree = HexagonCover.NBand.M6667_6700.SplitData.node0999 := by
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
  · exact treeEq1000

def B0998 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724991292464235241714316944097148992] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B0999, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq0998 : B0998.tree = HexagonCover.NBand.M6667_6700.SplitData.node0998 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0999
  · rfl
  · rfl

def B0989 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B0990, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0998, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq0989 : B0989.tree = HexagonCover.NBand.M6667_6700.SplitData.node0989 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0990
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0998
  · rfl

def B1003 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1003 : B1003.tree = HexagonCover.NBand.M6667_6700.SplitData.node1003 := by
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

def B1002 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1003]
theorem treeEq1002 : B1002.tree = HexagonCover.NBand.M6667_6700.SplitData.node1002 := by
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
  · exact treeEq1003

def B1001 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1002, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1001 : B1001.tree = HexagonCover.NBand.M6667_6700.SplitData.node1001 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1002
  · rfl
  · rfl

def B0988 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B0989, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1001]
theorem treeEq0988 : B0988.tree = HexagonCover.NBand.M6667_6700.SplitData.node0988 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0989
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1001

def B0971 : Block := .branch 74 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip0971_0972, B0988, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 1024).pointIds 1024)]
theorem treeEq0971 : B0971.tree = HexagonCover.NBand.M6667_6700.SplitData.node0971 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0988
  · rfl
  · rfl
  · rfl

theorem accepted0971 : B0971.accepted = true := by decide +kernel
theorem checked0971 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0971 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776]) := by
  rw [← treeEq0971]
  exact B0971.sound accepted0971
#print axioms checked0971

end HexagonCover.NBand.M6667_6700.SplitTree.Run0012
