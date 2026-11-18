import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0034
import HexagonCover.NBand.M8300_8500.SplitTree.Run0035
import HexagonCover.NBand.M8300_8500.SplitTree.Run0037
import HexagonCover.NBand.M8300_8500.SplitTree.Run0038
import HexagonCover.NBand.M8300_8500.SplitTree.Run0040
import HexagonCover.NBand.M8300_8500.SplitTree.Run0041
import HexagonCover.NBand.M8300_8500.SplitTree.Run0042
import HexagonCover.NBand.M8300_8500.SplitTree.Run0043
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0044
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip2389_2392 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2392 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0034.checked2392
def Tip2389_2533 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2533 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0035.checked2533
def Tip2389_2608 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2608 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0037.checked2608
def Tip2389_2736 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2736 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0038.checked2736
def B2531 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2531 : B2531.tree = HexagonCover.NBand.M8300_8500.SplitData.node2531 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2530 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2531, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2530 : B2530.tree = HexagonCover.NBand.M8300_8500.SplitData.node2530 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2531
  · rfl

def B2529 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237703830355906846847427174408, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2530]
theorem treeEq2529 : B2529.tree = HexagonCover.NBand.M8300_8500.SplitData.node2529 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2530

def B2391 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2389_2392, B2529, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2391 : B2391.tree = HexagonCover.NBand.M8300_8500.SplitData.node2391 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2529
  · rfl
  · rfl
  · rfl

def B2605 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2605 : B2605.tree = HexagonCover.NBand.M8300_8500.SplitData.node2605 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2604 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2605, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2604 : B2604.tree = HexagonCover.NBand.M8300_8500.SplitData.node2604 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2605
  · rfl

def B2603 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237713501762463763880824823816, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2604]
theorem treeEq2603 : B2603.tree = HexagonCover.NBand.M8300_8500.SplitData.node2603 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2604

def B2532 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2389_2533, B2603, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2532 : B2532.tree = HexagonCover.NBand.M8300_8500.SplitData.node2532 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2603
  · rfl
  · rfl
  · rfl

def B2390 : Block := .branch 83 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B2391, B2532, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq2390 : B2390.tree = HexagonCover.NBand.M8300_8500.SplitData.node2390 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2391
  · exact treeEq2532
  · rfl
  · rfl
  · rfl

def B2734 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2734 : B2734.tree = HexagonCover.NBand.M8300_8500.SplitData.node2734 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2733 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2734, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2733 : B2733.tree = HexagonCover.NBand.M8300_8500.SplitData.node2733 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2734
  · rfl

def B2732 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2733]
theorem treeEq2732 : B2732.tree = HexagonCover.NBand.M8300_8500.SplitData.node2732 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2733

def B2607 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2389_2608, B2732, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2607 : B2607.tree = HexagonCover.NBand.M8300_8500.SplitData.node2607 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2732
  · rfl
  · rfl
  · rfl

def B2808 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2808 : B2808.tree = HexagonCover.NBand.M8300_8500.SplitData.node2808 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2807 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2808, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2807 : B2807.tree = HexagonCover.NBand.M8300_8500.SplitData.node2807 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2808
  · rfl

def B2806 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2807]
theorem treeEq2806 : B2806.tree = HexagonCover.NBand.M8300_8500.SplitData.node2806 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2807

def B2735 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2389_2736, B2806, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2735 : B2735.tree = HexagonCover.NBand.M8300_8500.SplitData.node2735 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2806
  · rfl
  · rfl
  · rfl

def B2606 : Block := .branch 83 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B2607, B2735, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq2606 : B2606.tree = HexagonCover.NBand.M8300_8500.SplitData.node2606 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2607
  · exact treeEq2735
  · rfl
  · rfl
  · rfl

def B2389 : Block := .branch 82 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B2390, B2606, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq2389 : B2389.tree = HexagonCover.NBand.M8300_8500.SplitData.node2389 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2390
  · exact treeEq2606
  · rfl
  · rfl
  · rfl

theorem accepted2389 : B2389.accepted = true := by decide +kernel
theorem checked2389 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2389 (maskNeeds ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq2389]
  exact B2389.sound accepted2389
#print axioms checked2389

def Tip2388_2812 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2812 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0040.checked2812
def Tip2388_2953 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2953 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0041.checked2953
def Tip2388_3028 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node3028 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0042.checked3028
def Tip2388_3156 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node3156 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0043.checked3156
def Tip2388_2389 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2389 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked2389
def B2951 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2951 : B2951.tree = HexagonCover.NBand.M8300_8500.SplitData.node2951 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2950 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2951, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2950 : B2950.tree = HexagonCover.NBand.M8300_8500.SplitData.node2950 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2951
  · rfl

def B2949 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237703830355906846847427174408, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2950]
theorem treeEq2949 : B2949.tree = HexagonCover.NBand.M8300_8500.SplitData.node2949 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2950

def B2811 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2388_2812, B2949, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2811 : B2811.tree = HexagonCover.NBand.M8300_8500.SplitData.node2811 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2949
  · rfl
  · rfl
  · rfl

def B3025 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3025 : B3025.tree = HexagonCover.NBand.M8300_8500.SplitData.node3025 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3024 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3025, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3024 : B3024.tree = HexagonCover.NBand.M8300_8500.SplitData.node3024 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3025
  · rfl

def B3023 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237713501762463763880824823816, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B3024]
theorem treeEq3023 : B3023.tree = HexagonCover.NBand.M8300_8500.SplitData.node3023 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3024

def B2952 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2388_2953, B3023, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2952 : B2952.tree = HexagonCover.NBand.M8300_8500.SplitData.node2952 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3023
  · rfl
  · rfl
  · rfl

def B2810 : Block := .branch 83 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B2811, B2952, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq2810 : B2810.tree = HexagonCover.NBand.M8300_8500.SplitData.node2810 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2811
  · exact treeEq2952
  · rfl
  · rfl
  · rfl

def B3154 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3154 : B3154.tree = HexagonCover.NBand.M8300_8500.SplitData.node3154 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3153 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3154, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3153 : B3153.tree = HexagonCover.NBand.M8300_8500.SplitData.node3153 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3154
  · rfl

def B3152 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B3153]
theorem treeEq3152 : B3152.tree = HexagonCover.NBand.M8300_8500.SplitData.node3152 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3153

def B3027 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2388_3028, B3152, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq3027 : B3027.tree = HexagonCover.NBand.M8300_8500.SplitData.node3027 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3152
  · rfl
  · rfl
  · rfl

def B3228 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3228 : B3228.tree = HexagonCover.NBand.M8300_8500.SplitData.node3228 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3227 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3228, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3227 : B3227.tree = HexagonCover.NBand.M8300_8500.SplitData.node3227 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3228
  · rfl

def B3226 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B3227]
theorem treeEq3226 : B3226.tree = HexagonCover.NBand.M8300_8500.SplitData.node3226 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3227

def B3155 : Block := .branch 84 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip2388_3156, B3226, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq3155 : B3155.tree = HexagonCover.NBand.M8300_8500.SplitData.node3155 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3226
  · rfl
  · rfl
  · rfl

def B3026 : Block := .branch 83 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B3027, B3155, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq3026 : B3026.tree = HexagonCover.NBand.M8300_8500.SplitData.node3026 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3027
  · exact treeEq3155
  · rfl
  · rfl
  · rfl

def B2809 : Block := .branch 82 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B2810, B3026, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq2809 : B2809.tree = HexagonCover.NBand.M8300_8500.SplitData.node2809 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2810
  · exact treeEq3026
  · rfl
  · rfl
  · rfl

def B2388 : Block := .branch 78 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip2388_2389, B2809, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq2388 : B2388.tree = HexagonCover.NBand.M8300_8500.SplitData.node2388 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2809
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2388 : B2388.accepted = true := by decide +kernel
theorem checked2388 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2388 (maskNeeds ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq2388]
  exact B2388.sound accepted2388
#print axioms checked2388

def B3277 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq3277 : B3277.tree = HexagonCover.NBand.M8300_8500.SplitData.node3277 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3276 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B3277, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq3276 : B3276.tree = HexagonCover.NBand.M8300_8500.SplitData.node3276 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3277
  · rfl
  · rfl

def B3275 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B3276, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq3275 : B3275.tree = HexagonCover.NBand.M8300_8500.SplitData.node3275 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3276
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3274 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B3275, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq3274 : B3274.tree = HexagonCover.NBand.M8300_8500.SplitData.node3274 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3275
  · rfl
  · rfl
  · rfl
  · rfl

def B3273 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B3274]
theorem treeEq3273 : B3273.tree = HexagonCover.NBand.M8300_8500.SplitData.node3273 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3274

def B3272 : Block := .branch 169 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90945226513406734606392204534210411307827216, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3273, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq3272 : B3272.tree = HexagonCover.NBand.M8300_8500.SplitData.node3272 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3273
  · rfl

def B3271 : Block := .branch 138 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596777369679693619805708936200280659296272, 233840261972944466912589573234605283144949207269408, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B3272, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq3271 : B3271.tree = HexagonCover.NBand.M8300_8500.SplitData.node3271 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3272
  · rfl
  · rfl

def B3270 : Block := .branch 165 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 187072209578355573530071658587684226515959365894176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B3271, (.leaf 0 [] 0)]
theorem treeEq3270 : B3270.tree = HexagonCover.NBand.M8300_8500.SplitData.node3270 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3271
  · rfl

def B3269 : Block := .branch 167 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B3270, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3269 : B3269.tree = HexagonCover.NBand.M8300_8500.SplitData.node3269 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3270
  · rfl

def B3268 : Block := .branch 146 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 1393799234013192623494581653220955196063760, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B3269, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq3268 : B3268.tree = HexagonCover.NBand.M8300_8500.SplitData.node3268 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3269
  · rfl
  · rfl

def B3267 : Block := .branch 170 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B3268, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3267 : B3267.tree = HexagonCover.NBand.M8300_8500.SplitData.node3267 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3268
  · rfl
  · rfl
  · rfl

theorem accepted3267 : B3267.accepted = true := by decide +kernel
theorem checked3267 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node3267 (maskNeeds ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 393248, 3367299783582620114145322302633222186454766830747712]) := by
  rw [← treeEq3267]
  exact B3267.sound accepted3267
#print axioms checked3267

def Tip3256_3267 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node3267 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 393248, 3367299783582620114145322302633222186454766830747712] checked3267
def B3266 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq3266 : B3266.tree = HexagonCover.NBand.M8300_8500.SplitData.node3266 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3265 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B3266, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq3265 : B3265.tree = HexagonCover.NBand.M8300_8500.SplitData.node3265 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3266
  · rfl
  · rfl

def B3264 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B3265, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq3264 : B3264.tree = HexagonCover.NBand.M8300_8500.SplitData.node3264 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3265
  · rfl
  · rfl

def B3263 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B3264, (.leaf 0 [] 0)]
theorem treeEq3263 : B3263.tree = HexagonCover.NBand.M8300_8500.SplitData.node3263 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3264
  · rfl

def B3262 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B3263, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3262 : B3262.tree = HexagonCover.NBand.M8300_8500.SplitData.node3262 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3263
  · rfl

def B3261 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B3262, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq3261 : B3261.tree = HexagonCover.NBand.M8300_8500.SplitData.node3261 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3262
  · rfl
  · rfl

def B3260 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 577).pointIds 577), B3261, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq3260 : B3260.tree = HexagonCover.NBand.M8300_8500.SplitData.node3260 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3261
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3259 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B3260, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq3259 : B3259.tree = HexagonCover.NBand.M8300_8500.SplitData.node3259 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3260
  · rfl
  · rfl
  · rfl
  · rfl

def B3258 : Block := .branch 170 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664613997892457936451903530140196872, 178405964247350013809434345442367324649783312, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B3259, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq3258 : B3258.tree = HexagonCover.NBand.M8300_8500.SplitData.node3258 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3259
  · rfl
  · rfl
  · rfl

def B3257 : Block := .branch 169 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 42535295865117307932921825928971419680, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B3258]
theorem treeEq3257 : B3257.tree = HexagonCover.NBand.M8300_8500.SplitData.node3257 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3258

def B3256 : Block := .branch 125 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B3257, Tip3256_3267]
theorem treeEq3256 : B3256.tree = HexagonCover.NBand.M8300_8500.SplitData.node3256 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3257
  · rfl

theorem accepted3256 : B3256.accepted = true := by decide +kernel
theorem checked3256 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node3256 (maskNeeds ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq3256]
  exact B3256.sound accepted3256
#print axioms checked3256

def B3318 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq3318 : B3318.tree = HexagonCover.NBand.M8300_8500.SplitData.node3318 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3317 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B3318, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq3317 : B3317.tree = HexagonCover.NBand.M8300_8500.SplitData.node3317 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3318
  · rfl
  · rfl

def B3316 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B3317, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq3316 : B3316.tree = HexagonCover.NBand.M8300_8500.SplitData.node3316 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3317
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3315 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B3316, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq3315 : B3315.tree = HexagonCover.NBand.M8300_8500.SplitData.node3315 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3316
  · rfl
  · rfl
  · rfl
  · rfl

def B3314 : Block := .branch 166 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783604371601068346665977420085189194389389376] ![B3315, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq3314 : B3314.tree = HexagonCover.NBand.M8300_8500.SplitData.node3314 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq3315
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3313 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 625).pointIds 625), B3314]
theorem treeEq3313 : B3313.tree = HexagonCover.NBand.M8300_8500.SplitData.node3313 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3314

def B3312 : Block := .branch 169 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90945226513406734606392204534210411307827216, 233840261972944508450964441513226311388919841030176, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3313, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq3312 : B3312.tree = HexagonCover.NBand.M8300_8500.SplitData.node3312 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3313
  · rfl

def B3311 : Block := .branch 138 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596777369679693619805708936200280659296272, 233840261972944508450964441513226311388919841030176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B3312, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq3311 : B3311.tree = HexagonCover.NBand.M8300_8500.SplitData.node3311 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3312
  · rfl
  · rfl

def B3310 : Block := .branch 165 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 187072209578355615068446526866305254759929999654944, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B3311, (.leaf 0 [] 0)]
theorem treeEq3310 : B3310.tree = HexagonCover.NBand.M8300_8500.SplitData.node3310 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3311
  · rfl

def B3309 : Block := .branch 167 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B3310, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3309 : B3309.tree = HexagonCover.NBand.M8300_8500.SplitData.node3309 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3310
  · rfl

def B3308 : Block := .branch 146 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B3309, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq3308 : B3308.tree = HexagonCover.NBand.M8300_8500.SplitData.node3308 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3309
  · rfl
  · rfl

def B3307 : Block := .branch 170 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B3308, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3307 : B3307.tree = HexagonCover.NBand.M8300_8500.SplitData.node3307 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3308
  · rfl
  · rfl
  · rfl

theorem accepted3307 : B3307.accepted = true := by decide +kernel
theorem checked3307 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node3307 (maskNeeds ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712]) := by
  rw [← treeEq3307]
  exact B3307.sound accepted3307
#print axioms checked3307

end HexagonCover.NBand.M8300_8500.SplitTree.Run0044
