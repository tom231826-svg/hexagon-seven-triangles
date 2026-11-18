import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0010
import HexagonCover.NBand.M8500_8700.SplitTree.Run0014
import HexagonCover.NBand.M8500_8700.SplitTree.Run0018
import HexagonCover.NBand.M8500_8700.SplitTree.Run0026
import HexagonCover.NBand.M8500_8700.SplitTree.Run0030
import HexagonCover.NBand.M8500_8700.SplitTree.Run0033
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0034
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1919_1923 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1923 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0030.checked1923
def B2192 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq2192 : B2192.tree = HexagonCover.NBand.M8500_8700.SplitData.node2192 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2191 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2192, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq2191 : B2191.tree = HexagonCover.NBand.M8500_8700.SplitData.node2191 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2192
  · rfl

def B2190 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2191]
theorem treeEq2190 : B2190.tree = HexagonCover.NBand.M8500_8700.SplitData.node2190 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2191

def B1922 : Block := .branch 84 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), Tip1919_1923, B2190, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq1922 : B1922.tree = HexagonCover.NBand.M8500_8700.SplitData.node1922 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2190
  · rfl
  · rfl
  · rfl

def B2195 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq2195 : B2195.tree = HexagonCover.NBand.M8500_8700.SplitData.node2195 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2194 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2195, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq2194 : B2194.tree = HexagonCover.NBand.M8500_8700.SplitData.node2194 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2195
  · rfl

def B2193 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2194]
theorem treeEq2193 : B2193.tree = HexagonCover.NBand.M8500_8700.SplitData.node2193 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2194

def B1921 : Block := .branch 83 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B1922, B2193, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq1921 : B1921.tree = HexagonCover.NBand.M8500_8700.SplitData.node1921 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1922
  · exact treeEq2193
  · rfl
  · rfl
  · rfl

def B2200 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 748288838313422294120286634350736906063837462396960, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq2200 : B2200.tree = HexagonCover.NBand.M8500_8700.SplitData.node2200 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2199 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2996078367722322259844610718467484198196587523473472] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), B2200, (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq2199 : B2199.tree = HexagonCover.NBand.M8500_8700.SplitData.node2199 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2200
  · rfl

def B2198 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2199]
theorem treeEq2198 : B2198.tree = HexagonCover.NBand.M8500_8700.SplitData.node2198 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2199

def B2197 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2198, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq2197 : B2197.tree = HexagonCover.NBand.M8500_8700.SplitData.node2197 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2198
  · rfl
  · rfl
  · rfl

def B2196 : Block := .branch 161 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 925).pointIds 925), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B2197]
theorem treeEq2196 : B2196.tree = HexagonCover.NBand.M8500_8700.SplitData.node2196 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2197

def B1920 : Block := .branch 82 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B1921, B2196, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq1920 : B1920.tree = HexagonCover.NBand.M8500_8700.SplitData.node1920 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1921
  · exact treeEq2196
  · rfl
  · rfl
  · rfl

def B2203 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2203 : B2203.tree = HexagonCover.NBand.M8500_8700.SplitData.node2203 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2202 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2203, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq2202 : B2202.tree = HexagonCover.NBand.M8500_8700.SplitData.node2202 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2203
  · rfl
  · rfl
  · rfl

def B2201 : Block := .branch 160 ![1237940039864092827016233345, 528905082110747038713346, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 924).pointIds 924), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2202]
theorem treeEq2201 : B2201.tree = HexagonCover.NBand.M8500_8700.SplitData.node2201 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2202

def B1919 : Block := .branch 78 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B1920, B2201, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq1919 : B1919.tree = HexagonCover.NBand.M8500_8700.SplitData.node1919 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1920
  · exact treeEq2201
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1919 : B1919.accepted = true := by decide +kernel
theorem checked1919 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1919 (maskNeeds ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq1919]
  exact B1919.sound accepted1919
#print axioms checked1919

def Tip1918_2208 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node2208 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0033.checked2208
def Tip1918_1919 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1919 ![1237940039864092827016233345, 226673627207089745036802, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] checked1919
def B2477 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq2477 : B2477.tree = HexagonCover.NBand.M8500_8700.SplitData.node2477 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2476 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2477, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq2476 : B2476.tree = HexagonCover.NBand.M8500_8700.SplitData.node2476 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2477
  · rfl

def B2475 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2476]
theorem treeEq2475 : B2475.tree = HexagonCover.NBand.M8500_8700.SplitData.node2475 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2476

def B2207 : Block := .branch 84 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), Tip1918_2208, B2475, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq2207 : B2207.tree = HexagonCover.NBand.M8500_8700.SplitData.node2207 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2475
  · rfl
  · rfl
  · rfl

def B2480 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq2480 : B2480.tree = HexagonCover.NBand.M8500_8700.SplitData.node2480 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2479 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2480, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq2479 : B2479.tree = HexagonCover.NBand.M8500_8700.SplitData.node2479 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2480
  · rfl

def B2478 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2479]
theorem treeEq2478 : B2478.tree = HexagonCover.NBand.M8500_8700.SplitData.node2478 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2479

def B2206 : Block := .branch 83 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B2207, B2478, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq2206 : B2206.tree = HexagonCover.NBand.M8500_8700.SplitData.node2206 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2207
  · exact treeEq2478
  · rfl
  · rfl
  · rfl

def B2485 : Block := .branch 170 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 748288838313422294120286634350736906063837462396960, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 921).pointIds 921), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq2485 : B2485.tree = HexagonCover.NBand.M8500_8700.SplitData.node2485 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2484 : Block := .branch 169 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2996078367722322259844610718467484198196587523473472] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 923).pointIds 923), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), B2485, (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq2484 : B2484.tree = HexagonCover.NBand.M8500_8700.SplitData.node2484 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2485
  · rfl

def B2483 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2484]
theorem treeEq2483 : B2483.tree = HexagonCover.NBand.M8500_8700.SplitData.node2483 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2484

def B2482 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2483, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq2482 : B2482.tree = HexagonCover.NBand.M8500_8700.SplitData.node2482 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2483
  · rfl
  · rfl
  · rfl

def B2481 : Block := .branch 161 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 925).pointIds 925), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B2482]
theorem treeEq2481 : B2481.tree = HexagonCover.NBand.M8500_8700.SplitData.node2481 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2482

def B2205 : Block := .branch 82 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B2206, B2481, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq2205 : B2205.tree = HexagonCover.NBand.M8500_8700.SplitData.node2205 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2206
  · exact treeEq2481
  · rfl
  · rfl
  · rfl

def B2488 : Block := .branch 171 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2488 : B2488.tree = HexagonCover.NBand.M8500_8700.SplitData.node2488 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2487 : Block := .branch 172 ![1237940039864092827016233345, 151115763481175421617666, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 916).pointIds 916), (.leaf 2 (Common.fact 917).pointIds 917), B2488, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq2487 : B2487.tree = HexagonCover.NBand.M8500_8700.SplitData.node2487 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2488
  · rfl
  · rfl
  · rfl

def B2486 : Block := .branch 160 ![1237940039864092827016233345, 453347218384832715294210, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 927).pointIds 927), (.leaf 2 (Common.fact 924).pointIds 924), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B2487]
theorem treeEq2486 : B2486.tree = HexagonCover.NBand.M8500_8700.SplitData.node2486 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2487

def B2204 : Block := .branch 78 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B2205, B2486, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq2204 : B2204.tree = HexagonCover.NBand.M8500_8700.SplitData.node2204 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2205
  · exact treeEq2486
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1918 : Block := .branch 76 ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), Tip1918_1919, B2204, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq1918 : B1918.tree = HexagonCover.NBand.M8500_8700.SplitData.node1918 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2204
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1918 : B1918.accepted = true := by decide +kernel
theorem checked1918 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1918 (maskNeeds ![1237940039864092827016233345, 151115763481175421617666, 37834272095178290370564, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq1918]
  exact B1918.sound accepted1918
#print axioms checked1918

def Tip0039_0513 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0513 ![1238242271318996484309909889, 226673591178292726072834, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0010.checked0513
def Tip0039_0043 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0043 ![1238242271318996484309909889, 226673591178292726072834, 4873500657065547570092036, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0010.checked0043
def Tip0039_0793 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0793 ![1237940335011998006369059201, 377789318630121372911106, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0014.checked0793
def Tip0039_1071 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1071 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0018.checked1071
def Tip0039_1357 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1357 ![1237940039864092827016233345, 151447768845705174582786, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0026.checked1357
def B0786 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0786 : B0786.tree = HexagonCover.NBand.M8500_8700.SplitData.node0786 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0785 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0786, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0785 : B0785.tree = HexagonCover.NBand.M8500_8700.SplitData.node0785 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0786
  · rfl

def B0784 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158499846358034801837377347592, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0785]
theorem treeEq0784 : B0784.tree = HexagonCover.NBand.M8500_8700.SplitData.node0784 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0785

def B0512 : Block := .branch 85 ![1238242271318996484309909889, 226673591178292726072834, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), Tip0039_0513, B0784, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq0512 : B0512.tree = HexagonCover.NBand.M8500_8700.SplitData.node0512 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0784
  · rfl
  · rfl
  · rfl

def B0789 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0789 : B0789.tree = HexagonCover.NBand.M8500_8700.SplitData.node0789 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0788 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0789, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0788 : B0788.tree = HexagonCover.NBand.M8500_8700.SplitData.node0788 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0789
  · rfl

def B0787 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158480503544920967770582048776, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 863).pointIds 863), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0788]
theorem treeEq0787 : B0787.tree = HexagonCover.NBand.M8500_8700.SplitData.node0787 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0788

def B0511 : Block := .branch 84 ![1238242271318996484309909889, 226673591178292726072834, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B0512, B0787, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq0511 : B0511.tree = HexagonCover.NBand.M8500_8700.SplitData.node0511 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0512
  · exact treeEq0787
  · rfl
  · rfl
  · rfl

def B0792 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0792 : B0792.tree = HexagonCover.NBand.M8500_8700.SplitData.node0792 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0791 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0792, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0791 : B0791.tree = HexagonCover.NBand.M8500_8700.SplitData.node0791 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0792
  · rfl

def B0790 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0791]
theorem treeEq0790 : B0790.tree = HexagonCover.NBand.M8500_8700.SplitData.node0790 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0791

def B0510 : Block := .branch 83 ![1238242271318996484309909889, 226673591178292726072834, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B0511, B0790, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq0510 : B0510.tree = HexagonCover.NBand.M8500_8700.SplitData.node0510 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0511
  · exact treeEq0790
  · rfl
  · rfl
  · rfl

def B0042 : Block := .branch 82 ![1238242271318996484309909889, 226673591178292726072834, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), Tip0039_0043, B0510, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M8500_8700.SplitData.node0042 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0510
  · rfl
  · rfl
  · rfl

def B0041 : Block := .branch 78 ![1237940335011998006369059201, 226673591178292726072834, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B0042, Tip0039_0793, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M8500_8700.SplitData.node0041 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0042
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0040 : Block := .branch 76 ![1237940335011998006369059201, 151152620940525821756930, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), B0041, Tip0039_1071, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M8500_8700.SplitData.node0040 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0041
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1916 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq1916 : B1916.tree = HexagonCover.NBand.M8500_8700.SplitData.node1916 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1915 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 889).pointIds 889), B1916, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq1915 : B1915.tree = HexagonCover.NBand.M8500_8700.SplitData.node1915 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1916
  · rfl
  · rfl
  · rfl

def B1914 : Block := .branch 160 ![1237940039864092827016233345, 151447768845705174582786, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B1915]
theorem treeEq1914 : B1914.tree = HexagonCover.NBand.M8500_8700.SplitData.node1914 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1915

def B1356 : Block := .branch 76 ![1237940039864092827016233345, 151447768845705174582786, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), Tip0039_1357, B1914, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq1356 : B1356.tree = HexagonCover.NBand.M8500_8700.SplitData.node1356 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1914
  · rfl
  · rfl
  · rfl
  · rfl

def B0039 : Block := .branch 68 ![1237940039864092827016233345, 151152620940525821756930, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B0040, B1356, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M8500_8700.SplitData.node0039 := by
  change Tree.branch (68 : Fin 175) _ = Tree.branch (68 : Fin 175) _
  apply congrArg (Tree.branch (68 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0040
  · exact treeEq1356
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0039 : B0039.accepted = true := by decide +kernel
theorem checked0039 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0039 (maskNeeds ![1237940039864092827016233345, 151152620940525821756930, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq0039]
  exact B0039.sound accepted0039
#print axioms checked0039

def B2512 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq2512 : B2512.tree = HexagonCover.NBand.M8500_8700.SplitData.node2512 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2511 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2512, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq2511 : B2511.tree = HexagonCover.NBand.M8500_8700.SplitData.node2511 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2512
  · rfl

def B2510 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2511]
theorem treeEq2510 : B2510.tree = HexagonCover.NBand.M8500_8700.SplitData.node2510 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2511

def B2509 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 868).pointIds 868), B2510, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq2509 : B2509.tree = HexagonCover.NBand.M8500_8700.SplitData.node2509 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2510
  · rfl
  · rfl
  · rfl

def B2508 : Block := .branch 159 ![5192298715444886558852708491592065, 151116339941927725041154, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 929).pointIds 929), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B2509]
theorem treeEq2508 : B2508.tree = HexagonCover.NBand.M8500_8700.SplitData.node2508 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2509

def B2518 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq2518 : B2518.tree = HexagonCover.NBand.M8500_8700.SplitData.node2518 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2517 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2518, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq2517 : B2517.tree = HexagonCover.NBand.M8500_8700.SplitData.node2517 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2518
  · rfl

def B2516 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2517]
theorem treeEq2516 : B2516.tree = HexagonCover.NBand.M8500_8700.SplitData.node2516 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2517

def B2515 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 868).pointIds 868), B2516, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2515 : B2515.tree = HexagonCover.NBand.M8500_8700.SplitData.node2515 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2516
  · rfl
  · rfl
  · rfl

def B2514 : Block := .branch 159 ![10385863224579942416784701524017537, 151116339941927725041154, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 939).pointIds 939), (.leaf 1 (Common.fact 930).pointIds 930), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B2515]
theorem treeEq2514 : B2514.tree = HexagonCover.NBand.M8500_8700.SplitData.node2514 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2515

def B2522 : Block := .branch 169 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 938).pointIds 938), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2522 : B2522.tree = HexagonCover.NBand.M8500_8700.SplitData.node2522 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2521 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2522, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2521 : B2521.tree = HexagonCover.NBand.M8500_8700.SplitData.node2521 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2522
  · rfl

def B2520 : Block := .branch 171 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 934).pointIds 934), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B2521]
theorem treeEq2520 : B2520.tree = HexagonCover.NBand.M8500_8700.SplitData.node2520 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2521

def B2519 : Block := .branch 172 ![1237940039287632074712809857, 151116339941927725041154, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 868).pointIds 868), B2520, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2519 : B2519.tree = HexagonCover.NBand.M8500_8700.SplitData.node2519 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2520
  · rfl
  · rfl
  · rfl

def B2513 : Block := .branch 113 ![1269507510287159723708865577345, 151116339941927725041154, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B2514, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B2519]
theorem treeEq2513 : B2513.tree = HexagonCover.NBand.M8500_8700.SplitData.node2513 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2514
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2519

def B2507 : Block := .branch 112 ![1269507510287159723708865577345, 151116339941927725041154, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B2508, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B2513]
theorem treeEq2507 : B2507.tree = HexagonCover.NBand.M8500_8700.SplitData.node2507 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq2508
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2513

def B2524 : Block := .branch 168 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 941).pointIds 941), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq2524 : B2524.tree = HexagonCover.NBand.M8500_8700.SplitData.node2524 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2523 : Block := .branch 170 ![1237940039287632074712809857, 151116339941927725041154, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 936).pointIds 936), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B2524, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq2523 : B2523.tree = HexagonCover.NBand.M8500_8700.SplitData.node2523 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2524
  · rfl

def B2506 : Block := .branch 109 ![1269507510287159723708865577345, 151116339941927725041154, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B2507, (.leaf 5 (Common.fact 294).pointIds 294), B2523]
theorem treeEq2506 : B2506.tree = HexagonCover.NBand.M8500_8700.SplitData.node2506 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2507
  · rfl
  · exact treeEq2523

theorem accepted2506 : B2506.accepted = true := by decide +kernel
theorem checked2506 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node2506 (maskNeeds ![1269507510287159723708865577345, 151116339941927725041154, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq2506]
  exact B2506.sound accepted2506
#print axioms checked2506

end HexagonCover.NBand.M8500_8700.SplitTree.Run0034
