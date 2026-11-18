import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0075
import HexagonCover.NBand.M8300_8500.SplitTree.Run0077
import HexagonCover.NBand.M8300_8500.SplitTree.Run0078
import HexagonCover.NBand.M8300_8500.SplitTree.Run0080
import HexagonCover.NBand.M8300_8500.SplitTree.Run0081
import HexagonCover.NBand.M8300_8500.SplitTree.Run0083
import HexagonCover.NBand.M8300_8500.SplitTree.Run0084
import HexagonCover.NBand.M8300_8500.SplitTree.Run0085
import HexagonCover.NBand.M8300_8500.SplitTree.Run0086
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0087
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip5493_5496 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5496 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0077.checked5496
def Tip5493_5637 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5637 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237694158949349929814029525000, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0078.checked5637
def Tip5493_5712 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5712 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0080.checked5712
def Tip5493_5840 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5840 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237698994652628388330728349704, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0081.checked5840
def B5635 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5635 : B5635.tree = HexagonCover.NBand.M8300_8500.SplitData.node5635 := by
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

def B5634 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5635, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5634 : B5634.tree = HexagonCover.NBand.M8300_8500.SplitData.node5634 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5635
  · rfl

def B5633 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237703830355906846847427174408, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5634]
theorem treeEq5633 : B5633.tree = HexagonCover.NBand.M8300_8500.SplitData.node5633 := by
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
  · exact treeEq5634

def B5495 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5493_5496, B5633, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq5495 : B5495.tree = HexagonCover.NBand.M8300_8500.SplitData.node5495 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5633
  · rfl
  · rfl
  · rfl

def B5709 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5709 : B5709.tree = HexagonCover.NBand.M8300_8500.SplitData.node5709 := by
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

def B5708 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5709, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5708 : B5708.tree = HexagonCover.NBand.M8300_8500.SplitData.node5708 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5709
  · rfl

def B5707 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237713501762463763880824823816, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5708]
theorem treeEq5707 : B5707.tree = HexagonCover.NBand.M8300_8500.SplitData.node5707 := by
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
  · exact treeEq5708

def B5636 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237694158949349929814029525000, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5493_5637, B5707, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq5636 : B5636.tree = HexagonCover.NBand.M8300_8500.SplitData.node5636 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5707
  · rfl
  · rfl
  · rfl

def B5494 : Block := .branch 83 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B5495, B5636, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq5494 : B5494.tree = HexagonCover.NBand.M8300_8500.SplitData.node5494 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5495
  · exact treeEq5636
  · rfl
  · rfl
  · rfl

def B5838 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5838 : B5838.tree = HexagonCover.NBand.M8300_8500.SplitData.node5838 := by
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

def B5837 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5838, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5837 : B5837.tree = HexagonCover.NBand.M8300_8500.SplitData.node5837 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5838
  · rfl

def B5836 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237708666059185305364125999112, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5837]
theorem treeEq5836 : B5836.tree = HexagonCover.NBand.M8300_8500.SplitData.node5836 := by
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
  · exact treeEq5837

def B5711 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5493_5712, B5836, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq5711 : B5711.tree = HexagonCover.NBand.M8300_8500.SplitData.node5711 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5836
  · rfl
  · rfl
  · rfl

def B5912 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5912 : B5912.tree = HexagonCover.NBand.M8300_8500.SplitData.node5912 := by
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

def B5911 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5912, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5911 : B5911.tree = HexagonCover.NBand.M8300_8500.SplitData.node5911 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5912
  · rfl

def B5910 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237708666059185305364125999112, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5911]
theorem treeEq5910 : B5910.tree = HexagonCover.NBand.M8300_8500.SplitData.node5910 := by
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
  · exact treeEq5911

def B5839 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237698994652628388330728349704, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5493_5840, B5910, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq5839 : B5839.tree = HexagonCover.NBand.M8300_8500.SplitData.node5839 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5910
  · rfl
  · rfl
  · rfl

def B5710 : Block := .branch 83 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B5711, B5839, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq5710 : B5710.tree = HexagonCover.NBand.M8300_8500.SplitData.node5710 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5711
  · exact treeEq5839
  · rfl
  · rfl
  · rfl

def B5493 : Block := .branch 82 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B5494, B5710, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq5493 : B5493.tree = HexagonCover.NBand.M8300_8500.SplitData.node5493 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5494
  · exact treeEq5710
  · rfl
  · rfl
  · rfl

theorem accepted5493 : B5493.accepted = true := by decide +kernel
theorem checked5493 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5493 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5493]
  exact B5493.sound accepted5493
#print axioms checked5493

def Tip5492_5916 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5916 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0083.checked5916
def Tip5492_6057 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6057 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237694158949349929814029525000, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0084.checked6057
def Tip5492_6132 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6132 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0085.checked6132
def Tip5492_6260 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6260 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237698994652628388330728349704, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0086.checked6260
def Tip5492_5493 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5493 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked5493
def B6055 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq6055 : B6055.tree = HexagonCover.NBand.M8300_8500.SplitData.node6055 := by
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

def B6054 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B6055, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq6054 : B6054.tree = HexagonCover.NBand.M8300_8500.SplitData.node6054 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6055
  · rfl

def B6053 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237703830355906846847427174408, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6054]
theorem treeEq6053 : B6053.tree = HexagonCover.NBand.M8300_8500.SplitData.node6053 := by
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
  · exact treeEq6054

def B5915 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5492_5916, B6053, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq5915 : B5915.tree = HexagonCover.NBand.M8300_8500.SplitData.node5915 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6053
  · rfl
  · rfl
  · rfl

def B6129 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq6129 : B6129.tree = HexagonCover.NBand.M8300_8500.SplitData.node6129 := by
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

def B6128 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B6129, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq6128 : B6128.tree = HexagonCover.NBand.M8300_8500.SplitData.node6128 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6129
  · rfl

def B6127 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237713501762463763880824823816, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6128]
theorem treeEq6127 : B6127.tree = HexagonCover.NBand.M8300_8500.SplitData.node6127 := by
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
  · exact treeEq6128

def B6056 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237694158949349929814029525000, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5492_6057, B6127, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq6056 : B6056.tree = HexagonCover.NBand.M8300_8500.SplitData.node6056 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6127
  · rfl
  · rfl
  · rfl

def B5914 : Block := .branch 83 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B5915, B6056, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq5914 : B5914.tree = HexagonCover.NBand.M8300_8500.SplitData.node5914 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5915
  · exact treeEq6056
  · rfl
  · rfl
  · rfl

def B6258 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq6258 : B6258.tree = HexagonCover.NBand.M8300_8500.SplitData.node6258 := by
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

def B6257 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B6258, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq6257 : B6257.tree = HexagonCover.NBand.M8300_8500.SplitData.node6257 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6258
  · rfl

def B6256 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237708666059185305364125999112, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6257]
theorem treeEq6256 : B6256.tree = HexagonCover.NBand.M8300_8500.SplitData.node6256 := by
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
  · exact treeEq6257

def B6131 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5492_6132, B6256, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq6131 : B6131.tree = HexagonCover.NBand.M8300_8500.SplitData.node6131 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6256
  · rfl
  · rfl
  · rfl

def B6332 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq6332 : B6332.tree = HexagonCover.NBand.M8300_8500.SplitData.node6332 := by
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

def B6331 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B6332, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq6331 : B6331.tree = HexagonCover.NBand.M8300_8500.SplitData.node6331 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6332
  · rfl

def B6330 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237708666059185305364125999112, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6331]
theorem treeEq6330 : B6330.tree = HexagonCover.NBand.M8300_8500.SplitData.node6330 := by
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
  · exact treeEq6331

def B6259 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237698994652628388330728349704, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip5492_6260, B6330, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq6259 : B6259.tree = HexagonCover.NBand.M8300_8500.SplitData.node6259 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6330
  · rfl
  · rfl
  · rfl

def B6130 : Block := .branch 83 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B6131, B6259, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq6130 : B6130.tree = HexagonCover.NBand.M8300_8500.SplitData.node6130 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6131
  · exact treeEq6259
  · rfl
  · rfl
  · rfl

def B5913 : Block := .branch 82 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B5914, B6130, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq5913 : B5913.tree = HexagonCover.NBand.M8300_8500.SplitData.node5913 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5914
  · exact treeEq6130
  · rfl
  · rfl
  · rfl

def B5492 : Block := .branch 78 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip5492_5493, B5913, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 1050).pointIds 1050)]
theorem treeEq5492 : B5492.tree = HexagonCover.NBand.M8300_8500.SplitData.node5492 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5913
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5492 : B5492.accepted = true := by decide +kernel
theorem checked5492 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5492 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5492]
  exact B5492.sound accepted5492
#print axioms checked5492

def Tip4637_4638 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4638 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0075.checked4638
def B5490 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq5490 : B5490.tree = HexagonCover.NBand.M8300_8500.SplitData.node5490 := by
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

def B5489 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5490, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq5489 : B5489.tree = HexagonCover.NBand.M8300_8500.SplitData.node5489 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5490
  · rfl

def B5488 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B5489, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq5488 : B5488.tree = HexagonCover.NBand.M8300_8500.SplitData.node5488 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5489
  · rfl
  · rfl
  · rfl
  · rfl

def B5487 : Block := .branch 85 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B5488, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq5487 : B5487.tree = HexagonCover.NBand.M8300_8500.SplitData.node5487 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5488
  · rfl
  · rfl
  · rfl
  · rfl

def B5486 : Block := .branch 86 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B5487, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq5486 : B5486.tree = HexagonCover.NBand.M8300_8500.SplitData.node5486 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5487
  · rfl
  · rfl
  · rfl
  · rfl

def B5485 : Block := .branch 138 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B5486, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5485 : B5485.tree = HexagonCover.NBand.M8300_8500.SplitData.node5485 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5486
  · rfl
  · rfl

def B5484 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5485, (.leaf 0 [] 0)]
theorem treeEq5484 : B5484.tree = HexagonCover.NBand.M8300_8500.SplitData.node5484 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5485
  · rfl

def B5483 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5484, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5483 : B5483.tree = HexagonCover.NBand.M8300_8500.SplitData.node5483 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5484
  · rfl

def B5482 : Block := .branch 146 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B5483, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5482 : B5482.tree = HexagonCover.NBand.M8300_8500.SplitData.node5482 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5483
  · rfl
  · rfl

def B5481 : Block := .branch 161 ![576460752303423873, 146437906389534210, 80298676952857678190596, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 900).pointIds 900), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B5482]
theorem treeEq5481 : B5481.tree = HexagonCover.NBand.M8300_8500.SplitData.node5481 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5482

def B5480 : Block := .branch 170 ![576460752303423873, 146437906389534210, 80298676952857678190596, 79228162514264337593543974920, 1393796575557201053662835845606834635374608, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5481, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq5480 : B5480.tree = HexagonCover.NBand.M8300_8500.SplitData.node5480 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5481
  · rfl
  · rfl
  · rfl

def B5479 : Block := .branch 160 ![576460752303423873, 146437906389534210, 80298676952857678190596, 79228162514264337593543974920, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), (.leaf 2 (Common.fact 989).pointIds 989), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B5480]
theorem treeEq5479 : B5479.tree = HexagonCover.NBand.M8300_8500.SplitData.node5479 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5480

def B4637 : Block := .branch 76 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip4637_4638, B5479, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 1049).pointIds 1049)]
theorem treeEq4637 : B4637.tree = HexagonCover.NBand.M8300_8500.SplitData.node4637 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5479
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4637 : B4637.accepted = true := by decide +kernel
theorem checked4637 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4637 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4637]
  exact B4637.sound accepted4637
#print axioms checked4637

def Tip4636_5492 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5492 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked5492
def Tip4636_4637 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4637 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked4637
def B6344 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq6344 : B6344.tree = HexagonCover.NBand.M8300_8500.SplitData.node6344 := by
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

def B6343 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B6344, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq6343 : B6343.tree = HexagonCover.NBand.M8300_8500.SplitData.node6343 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6344
  · rfl

def B6342 : Block := .branch 84 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B6343, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq6342 : B6342.tree = HexagonCover.NBand.M8300_8500.SplitData.node6342 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6343
  · rfl
  · rfl
  · rfl
  · rfl

def B6341 : Block := .branch 85 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B6342, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq6341 : B6341.tree = HexagonCover.NBand.M8300_8500.SplitData.node6341 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6342
  · rfl
  · rfl
  · rfl
  · rfl

def B6340 : Block := .branch 86 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6341, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq6340 : B6340.tree = HexagonCover.NBand.M8300_8500.SplitData.node6340 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6341
  · rfl
  · rfl
  · rfl
  · rfl

def B6339 : Block := .branch 138 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B6340, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq6339 : B6339.tree = HexagonCover.NBand.M8300_8500.SplitData.node6339 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6340
  · rfl
  · rfl

def B6338 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B6339, (.leaf 0 [] 0)]
theorem treeEq6338 : B6338.tree = HexagonCover.NBand.M8300_8500.SplitData.node6338 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6339
  · rfl

def B6337 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B6338, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6337 : B6337.tree = HexagonCover.NBand.M8300_8500.SplitData.node6337 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6338
  · rfl

def B6336 : Block := .branch 146 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6337, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6336 : B6336.tree = HexagonCover.NBand.M8300_8500.SplitData.node6336 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6337
  · rfl
  · rfl

def B6335 : Block := .branch 161 ![576460752303423873, 146437906389534210, 80298676952857678190596, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 900).pointIds 900), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B6336]
theorem treeEq6335 : B6335.tree = HexagonCover.NBand.M8300_8500.SplitData.node6335 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6336

def B6334 : Block := .branch 170 ![576460752303423873, 146437906389534210, 80298676952857678190596, 79228162514264337593543974920, 1393796575557201053662835845606834635374608, 393248, 3368761285219887214119728311504039086735529306751040] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6335, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq6334 : B6334.tree = HexagonCover.NBand.M8300_8500.SplitData.node6334 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6335
  · rfl
  · rfl
  · rfl

def B6333 : Block := .branch 160 ![576460752303423873, 146437906389534210, 80298676952857678190596, 79228162514264337593543974920, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), (.leaf 2 (Common.fact 989).pointIds 989), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B6334]
theorem treeEq6333 : B6333.tree = HexagonCover.NBand.M8300_8500.SplitData.node6333 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6334

def B5491 : Block := .branch 76 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip4636_5492, B6333, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 1049).pointIds 1049)]
theorem treeEq5491 : B5491.tree = HexagonCover.NBand.M8300_8500.SplitData.node5491 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6333
  · rfl
  · rfl
  · rfl
  · rfl

def B4636 : Block := .branch 68 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4636_4637, B5491, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1048).pointIds 1048)]
theorem treeEq4636 : B4636.tree = HexagonCover.NBand.M8300_8500.SplitData.node4636 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5491
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4636 : B4636.accepted = true := by decide +kernel
theorem checked4636 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4636 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237684487542793012780631875592, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4636]
  exact B4636.sound accepted4636
#print axioms checked4636

end HexagonCover.NBand.M8300_8500.SplitTree.Run0087
