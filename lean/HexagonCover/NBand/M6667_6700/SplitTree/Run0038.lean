import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0037
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0038
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2813_2814 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2814 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0037.checked2814
def B2833 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2833 : B2833.tree = HexagonCover.NBand.M6667_6700.SplitData.node2833 := by
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

def B2832 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2833, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2832 : B2832.tree = HexagonCover.NBand.M6667_6700.SplitData.node2832 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2833
  · rfl
  · rfl

def B2831 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2832]
theorem treeEq2831 : B2831.tree = HexagonCover.NBand.M6667_6700.SplitData.node2831 := by
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
  · exact treeEq2832

def B2836 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2836 : B2836.tree = HexagonCover.NBand.M6667_6700.SplitData.node2836 := by
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

def B2835 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2836]
theorem treeEq2835 : B2835.tree = HexagonCover.NBand.M6667_6700.SplitData.node2835 := by
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
  · exact treeEq2836

def B2834 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2835, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2834 : B2834.tree = HexagonCover.NBand.M6667_6700.SplitData.node2834 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2835
  · rfl
  · rfl

def B2830 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2831, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2834]
theorem treeEq2830 : B2830.tree = HexagonCover.NBand.M6667_6700.SplitData.node2830 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2831
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2834

def B2840 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2840 : B2840.tree = HexagonCover.NBand.M6667_6700.SplitData.node2840 := by
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

def B2839 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2840, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2839 : B2839.tree = HexagonCover.NBand.M6667_6700.SplitData.node2839 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2840
  · rfl
  · rfl

def B2838 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2839]
theorem treeEq2838 : B2838.tree = HexagonCover.NBand.M6667_6700.SplitData.node2838 := by
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
  · exact treeEq2839

def B2843 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2843 : B2843.tree = HexagonCover.NBand.M6667_6700.SplitData.node2843 := by
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

def B2842 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2843]
theorem treeEq2842 : B2842.tree = HexagonCover.NBand.M6667_6700.SplitData.node2842 := by
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
  · exact treeEq2843

def B2841 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2842, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2841 : B2841.tree = HexagonCover.NBand.M6667_6700.SplitData.node2841 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2842
  · rfl
  · rfl

def B2837 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2838, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2841]
theorem treeEq2837 : B2837.tree = HexagonCover.NBand.M6667_6700.SplitData.node2837 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2838
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2841

def B2829 : Block := .branch 74 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B2830, B2837, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2829 : B2829.tree = HexagonCover.NBand.M6667_6700.SplitData.node2829 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2830
  · exact treeEq2837
  · rfl
  · rfl
  · rfl

def B2813 : Block := .branch 73 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip2813_2814, B2829, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq2813 : B2813.tree = HexagonCover.NBand.M6667_6700.SplitData.node2813 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2829
  · rfl
  · rfl
  · rfl

theorem accepted2813 : B2813.accepted = true := by decide +kernel
theorem checked2813 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2813 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq2813]
  exact B2813.sound accepted2813
#print axioms checked2813

def Tip2812_2845 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2845 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0037.checked2845
def Tip2812_2813 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2813 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] checked2813
def B2864 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2864 : B2864.tree = HexagonCover.NBand.M6667_6700.SplitData.node2864 := by
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

def B2863 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2864, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2863 : B2863.tree = HexagonCover.NBand.M6667_6700.SplitData.node2863 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2864
  · rfl
  · rfl

def B2862 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2863]
theorem treeEq2862 : B2862.tree = HexagonCover.NBand.M6667_6700.SplitData.node2862 := by
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
  · exact treeEq2863

def B2867 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2867 : B2867.tree = HexagonCover.NBand.M6667_6700.SplitData.node2867 := by
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

def B2866 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2867]
theorem treeEq2866 : B2866.tree = HexagonCover.NBand.M6667_6700.SplitData.node2866 := by
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
  · exact treeEq2867

def B2865 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2866, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2865 : B2865.tree = HexagonCover.NBand.M6667_6700.SplitData.node2865 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2866
  · rfl
  · rfl

def B2861 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2862, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2865]
theorem treeEq2861 : B2861.tree = HexagonCover.NBand.M6667_6700.SplitData.node2861 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2862
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2865

def B2871 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2871 : B2871.tree = HexagonCover.NBand.M6667_6700.SplitData.node2871 := by
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

def B2870 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2871, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2870 : B2870.tree = HexagonCover.NBand.M6667_6700.SplitData.node2870 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2871
  · rfl
  · rfl

def B2869 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2870]
theorem treeEq2869 : B2869.tree = HexagonCover.NBand.M6667_6700.SplitData.node2869 := by
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
  · exact treeEq2870

def B2874 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2874 : B2874.tree = HexagonCover.NBand.M6667_6700.SplitData.node2874 := by
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

def B2873 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2874]
theorem treeEq2873 : B2873.tree = HexagonCover.NBand.M6667_6700.SplitData.node2873 := by
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
  · exact treeEq2874

def B2872 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2873, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2872 : B2872.tree = HexagonCover.NBand.M6667_6700.SplitData.node2872 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2873
  · rfl
  · rfl

def B2868 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2869, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2872]
theorem treeEq2868 : B2868.tree = HexagonCover.NBand.M6667_6700.SplitData.node2868 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2869
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2872

def B2860 : Block := .branch 74 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B2861, B2868, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2860 : B2860.tree = HexagonCover.NBand.M6667_6700.SplitData.node2860 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2861
  · exact treeEq2868
  · rfl
  · rfl
  · rfl

def B2844 : Block := .branch 73 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip2812_2845, B2860, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq2844 : B2844.tree = HexagonCover.NBand.M6667_6700.SplitData.node2844 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2860
  · rfl
  · rfl
  · rfl

def B2812 : Block := .branch 72 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), Tip2812_2813, B2844, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq2812 : B2812.tree = HexagonCover.NBand.M6667_6700.SplitData.node2812 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2844
  · rfl
  · rfl
  · rfl

theorem accepted2812 : B2812.accepted = true := by decide +kernel
theorem checked2812 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2812 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq2812]
  exact B2812.sound accepted2812
#print axioms checked2812

def Tip2732_2744 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2744 ![2596149667207453099645523063734657, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0037.checked2744
def Tip2732_2812 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2812 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] checked2812
def B2734 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2734 : B2734.tree = HexagonCover.NBand.M6667_6700.SplitData.node2734 := by
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

def B2733 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B2734]
theorem treeEq2733 : B2733.tree = HexagonCover.NBand.M6667_6700.SplitData.node2733 := by
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
  · exact treeEq2734

def B2737 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq2737 : B2737.tree = HexagonCover.NBand.M6667_6700.SplitData.node2737 := by
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

def B2736 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B2737]
theorem treeEq2736 : B2736.tree = HexagonCover.NBand.M6667_6700.SplitData.node2736 := by
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
  · exact treeEq2737

def B2743 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq2743 : B2743.tree = HexagonCover.NBand.M6667_6700.SplitData.node2743 := by
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

def B2742 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2743, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2742 : B2742.tree = HexagonCover.NBand.M6667_6700.SplitData.node2742 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2743
  · rfl
  · rfl

def B2741 : Block := .branch 158 ![5316911984377603530900608516020502913, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 1204).pointIds 1204), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2742]
theorem treeEq2741 : B2741.tree = HexagonCover.NBand.M6667_6700.SplitData.node2741 := by
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
  · exact treeEq2742

def B2740 : Block := .branch 163 ![5316911984377603530900608516020502913, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 1203).pointIds 1203), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2741]
theorem treeEq2740 : B2740.tree = HexagonCover.NBand.M6667_6700.SplitData.node2740 := by
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
  · exact treeEq2741

def B2739 : Block := .branch 122 ![2596149667207453099645523063734657, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B2740, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip2732_2744]
theorem treeEq2739 : B2739.tree = HexagonCover.NBand.M6667_6700.SplitData.node2739 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2740
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2811 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq2811 : B2811.tree = HexagonCover.NBand.M6667_6700.SplitData.node2811 := by
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

def B2810 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2811, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2810 : B2810.tree = HexagonCover.NBand.M6667_6700.SplitData.node2810 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2811
  · rfl
  · rfl

def B2809 : Block := .branch 158 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 1193).pointIds 1193), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2810]
theorem treeEq2809 : B2809.tree = HexagonCover.NBand.M6667_6700.SplitData.node2809 := by
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
  · exact treeEq2810

def B2808 : Block := .branch 163 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 1192).pointIds 1192), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2809]
theorem treeEq2808 : B2808.tree = HexagonCover.NBand.M6667_6700.SplitData.node2808 := by
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
  · exact treeEq2809

def B2807 : Block := .branch 122 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B2808, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip2732_2812]
theorem treeEq2807 : B2807.tree = HexagonCover.NBand.M6667_6700.SplitData.node2807 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2808
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2738 : Block := .branch 90 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B2739, B2807, (.leaf 2 (Common.fact 1194).pointIds 1194), (.leaf 3 (Common.fact 1195).pointIds 1195), (.leaf 4 (Common.fact 1196).pointIds 1196), (.leaf 5 (Common.fact 1197).pointIds 1197), (.leaf 6 (Common.fact 1202).pointIds 1202)]
theorem treeEq2738 : B2738.tree = HexagonCover.NBand.M6667_6700.SplitData.node2738 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2739
  · exact treeEq2807
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2735 : Block := .branch 121 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664091495163138109364451942813045360164928] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B2736, (.leaf 5 (Common.fact 430).pointIds 430), B2738]
theorem treeEq2735 : B2735.tree = HexagonCover.NBand.M6667_6700.SplitData.node2735 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2736
  · rfl
  · exact treeEq2738

def B2732 : Block := .branch 120 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B2733, (.leaf 5 (Common.fact 163).pointIds 163), B2735]
theorem treeEq2732 : B2732.tree = HexagonCover.NBand.M6667_6700.SplitData.node2732 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2733
  · rfl
  · exact treeEq2735

theorem accepted2732 : B2732.accepted = true := by decide +kernel
theorem checked2732 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2732 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352]) := by
  rw [← treeEq2732]
  exact B2732.sound accepted2732
#print axioms checked2732

def B2880 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq2880 : B2880.tree = HexagonCover.NBand.M6667_6700.SplitData.node2880 := by
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

def B2879 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2880]
theorem treeEq2879 : B2879.tree = HexagonCover.NBand.M6667_6700.SplitData.node2879 := by
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
  · exact treeEq2880

def B2883 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2883 : B2883.tree = HexagonCover.NBand.M6667_6700.SplitData.node2883 := by
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

def B2882 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2883]
theorem treeEq2882 : B2882.tree = HexagonCover.NBand.M6667_6700.SplitData.node2882 := by
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
  · exact treeEq2883

def B2881 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2882, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq2881 : B2881.tree = HexagonCover.NBand.M6667_6700.SplitData.node2881 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2882
  · rfl
  · rfl

def B2878 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2879, (.leaf 5 (Common.fact 419).pointIds 419), B2881]
theorem treeEq2878 : B2878.tree = HexagonCover.NBand.M6667_6700.SplitData.node2878 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2879
  · rfl
  · exact treeEq2881

def B2885 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq2885 : B2885.tree = HexagonCover.NBand.M6667_6700.SplitData.node2885 := by
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

def B2884 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2885, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq2884 : B2884.tree = HexagonCover.NBand.M6667_6700.SplitData.node2884 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2885
  · rfl
  · rfl

def B2877 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B2878, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B2884]
theorem treeEq2877 : B2877.tree = HexagonCover.NBand.M6667_6700.SplitData.node2877 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2878
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2884

def B2889 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq2889 : B2889.tree = HexagonCover.NBand.M6667_6700.SplitData.node2889 := by
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

def B2888 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2889]
theorem treeEq2888 : B2888.tree = HexagonCover.NBand.M6667_6700.SplitData.node2888 := by
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
  · exact treeEq2889

def B2892 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2892 : B2892.tree = HexagonCover.NBand.M6667_6700.SplitData.node2892 := by
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

def B2891 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2892]
theorem treeEq2891 : B2891.tree = HexagonCover.NBand.M6667_6700.SplitData.node2891 := by
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
  · exact treeEq2892

def B2890 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2891, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq2890 : B2890.tree = HexagonCover.NBand.M6667_6700.SplitData.node2890 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2891
  · rfl
  · rfl

def B2887 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2888, (.leaf 5 (Common.fact 419).pointIds 419), B2890]
theorem treeEq2887 : B2887.tree = HexagonCover.NBand.M6667_6700.SplitData.node2887 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2888
  · rfl
  · exact treeEq2890

def B2894 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq2894 : B2894.tree = HexagonCover.NBand.M6667_6700.SplitData.node2894 := by
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

def B2893 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2894, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq2893 : B2893.tree = HexagonCover.NBand.M6667_6700.SplitData.node2893 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2894
  · rfl
  · rfl

def B2886 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B2887, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B2893]
theorem treeEq2886 : B2886.tree = HexagonCover.NBand.M6667_6700.SplitData.node2886 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2887
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2893

def B2876 : Block := .branch 72 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B2877, B2886, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq2876 : B2876.tree = HexagonCover.NBand.M6667_6700.SplitData.node2876 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2877
  · exact treeEq2886
  · rfl
  · rfl
  · rfl

def B2875 : Block := .branch 139 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B2876, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq2875 : B2875.tree = HexagonCover.NBand.M6667_6700.SplitData.node2875 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2876
  · rfl
  · rfl

theorem accepted2875 : B2875.accepted = true := by decide +kernel
theorem checked2875 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2875 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656]) := by
  rw [← treeEq2875]
  exact B2875.sound accepted2875
#print axioms checked2875

end HexagonCover.NBand.M6667_6700.SplitTree.Run0038
