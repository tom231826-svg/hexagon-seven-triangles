import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0075
import HexagonCover.NBand.M8500_8700.SplitTree.Run0078
import HexagonCover.NBand.M8500_8700.SplitTree.Run0079
import HexagonCover.NBand.M8500_8700.SplitTree.Run0081
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0082
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip5341_5346 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5346 ![1238242271316744684496224641, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0075.checked5346
def Tip5341_5431 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5431 ![1238242271316744684496224641, 151115729774546960516610, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0078.checked5431
def B5421 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5421 : B5421.tree = HexagonCover.NBand.M8500_8700.SplitData.node5421 := by
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

def B5420 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5421, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5420 : B5420.tree = HexagonCover.NBand.M8500_8700.SplitData.node5420 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5421
  · rfl

def B5419 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5420]
theorem treeEq5419 : B5419.tree = HexagonCover.NBand.M8500_8700.SplitData.node5419 := by
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
  · exact treeEq5420

def B5345 : Block := .branch 86 ![1238242271316744684496224641, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), Tip5341_5346, B5419, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq5345 : B5345.tree = HexagonCover.NBand.M8500_8700.SplitData.node5345 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5419
  · rfl
  · rfl
  · rfl

def B5424 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5424 : B5424.tree = HexagonCover.NBand.M8500_8700.SplitData.node5424 := by
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

def B5423 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5424, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5423 : B5423.tree = HexagonCover.NBand.M8500_8700.SplitData.node5423 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5424
  · rfl

def B5422 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 882).pointIds 882), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5423]
theorem treeEq5422 : B5422.tree = HexagonCover.NBand.M8500_8700.SplitData.node5422 := by
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
  · exact treeEq5423

def B5344 : Block := .branch 85 ![1238242271316744684496224641, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B5345, B5422, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq5344 : B5344.tree = HexagonCover.NBand.M8500_8700.SplitData.node5344 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5345
  · exact treeEq5422
  · rfl
  · rfl
  · rfl

def B5427 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5427 : B5427.tree = HexagonCover.NBand.M8500_8700.SplitData.node5427 := by
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

def B5426 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5427, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5426 : B5426.tree = HexagonCover.NBand.M8500_8700.SplitData.node5426 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5427
  · rfl

def B5425 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5426]
theorem treeEq5425 : B5425.tree = HexagonCover.NBand.M8500_8700.SplitData.node5425 := by
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
  · exact treeEq5426

def B5343 : Block := .branch 84 ![1238242271316744684496224641, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B5344, B5425, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq5343 : B5343.tree = HexagonCover.NBand.M8500_8700.SplitData.node5343 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5344
  · exact treeEq5425
  · rfl
  · rfl
  · rfl

def B5430 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5430 : B5430.tree = HexagonCover.NBand.M8500_8700.SplitData.node5430 := by
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

def B5429 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5430, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5429 : B5429.tree = HexagonCover.NBand.M8500_8700.SplitData.node5429 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5430
  · rfl

def B5428 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5429]
theorem treeEq5428 : B5428.tree = HexagonCover.NBand.M8500_8700.SplitData.node5428 := by
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
  · exact treeEq5429

def B5342 : Block := .branch 83 ![1238242271316744684496224641, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B5343, B5428, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq5342 : B5342.tree = HexagonCover.NBand.M8500_8700.SplitData.node5342 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5343
  · exact treeEq5428
  · rfl
  · rfl
  · rfl

def B5341 : Block := .branch 82 ![1238242271316744684496224641, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B5342, Tip5341_5431, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq5341 : B5341.tree = HexagonCover.NBand.M8500_8700.SplitData.node5341 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5342
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5341 : B5341.accepted = true := by decide +kernel
theorem checked5341 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5341 (maskNeeds ![1238242271316744684496224641, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq5341]
  exact B5341.sound accepted5341
#print axioms checked5341

def Tip5340_5624 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5624 ![1237940039861841027202548097, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0079.checked5624
def Tip5340_5709 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5709 ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0081.checked5709
def Tip5340_5341 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5341 ![1238242271316744684496224641, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] checked5341
def B5699 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5699 : B5699.tree = HexagonCover.NBand.M8500_8700.SplitData.node5699 := by
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

def B5698 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5699, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5698 : B5698.tree = HexagonCover.NBand.M8500_8700.SplitData.node5698 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5699
  · rfl

def B5697 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5698]
theorem treeEq5697 : B5697.tree = HexagonCover.NBand.M8500_8700.SplitData.node5697 := by
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
  · exact treeEq5698

def B5623 : Block := .branch 86 ![1237940039861841027202548097, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), Tip5340_5624, B5697, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq5623 : B5623.tree = HexagonCover.NBand.M8500_8700.SplitData.node5623 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5697
  · rfl
  · rfl
  · rfl

def B5702 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5702 : B5702.tree = HexagonCover.NBand.M8500_8700.SplitData.node5702 := by
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

def B5701 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5702, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5701 : B5701.tree = HexagonCover.NBand.M8500_8700.SplitData.node5701 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5702
  · rfl

def B5700 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 882).pointIds 882), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5701]
theorem treeEq5700 : B5700.tree = HexagonCover.NBand.M8500_8700.SplitData.node5700 := by
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
  · exact treeEq5701

def B5622 : Block := .branch 85 ![1237940039861841027202548097, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B5623, B5700, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq5622 : B5622.tree = HexagonCover.NBand.M8500_8700.SplitData.node5622 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5623
  · exact treeEq5700
  · rfl
  · rfl
  · rfl

def B5705 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5705 : B5705.tree = HexagonCover.NBand.M8500_8700.SplitData.node5705 := by
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

def B5704 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5705, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5704 : B5704.tree = HexagonCover.NBand.M8500_8700.SplitData.node5704 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5705
  · rfl

def B5703 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5704]
theorem treeEq5703 : B5703.tree = HexagonCover.NBand.M8500_8700.SplitData.node5703 := by
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
  · exact treeEq5704

def B5621 : Block := .branch 84 ![1237940039861841027202548097, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B5622, B5703, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq5621 : B5621.tree = HexagonCover.NBand.M8500_8700.SplitData.node5621 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5622
  · exact treeEq5703
  · rfl
  · rfl
  · rfl

def B5708 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq5708 : B5708.tree = HexagonCover.NBand.M8500_8700.SplitData.node5708 := by
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

def B5707 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5708, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq5707 : B5707.tree = HexagonCover.NBand.M8500_8700.SplitData.node5707 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5708
  · rfl

def B5706 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5707]
theorem treeEq5706 : B5706.tree = HexagonCover.NBand.M8500_8700.SplitData.node5706 := by
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
  · exact treeEq5707

def B5620 : Block := .branch 83 ![1237940039861841027202548097, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B5621, B5706, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq5620 : B5620.tree = HexagonCover.NBand.M8500_8700.SplitData.node5620 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5621
  · exact treeEq5706
  · rfl
  · rfl
  · rfl

def B5619 : Block := .branch 82 ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B5620, Tip5340_5709, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq5619 : B5619.tree = HexagonCover.NBand.M8500_8700.SplitData.node5619 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5620
  · rfl
  · rfl
  · rfl
  · rfl

def B5340 : Block := .branch 78 ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![Tip5340_5341, B5619, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq5340 : B5340.tree = HexagonCover.NBand.M8500_8700.SplitData.node5340 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5619
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5340 : B5340.accepted = true := by decide +kernel
theorem checked5340 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5340 (maskNeeds ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq5340]
  exact B5340.sound accepted5340
#print axioms checked5340

def B5923 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq5923 : B5923.tree = HexagonCover.NBand.M8500_8700.SplitData.node5923 := by
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

def B5922 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5923, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq5922 : B5922.tree = HexagonCover.NBand.M8500_8700.SplitData.node5922 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5923
  · rfl

def B5921 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5922]
theorem treeEq5921 : B5921.tree = HexagonCover.NBand.M8500_8700.SplitData.node5921 := by
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
  · exact treeEq5922

def B5920 : Block := .branch 172 ![1237940334433285454251950465, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B5921, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq5920 : B5920.tree = HexagonCover.NBand.M8500_8700.SplitData.node5920 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5921
  · rfl
  · rfl
  · rfl

def B5919 : Block := .branch 159 ![5192298715445181704506088030732673, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 987).pointIds 987), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B5920]
theorem treeEq5919 : B5919.tree = HexagonCover.NBand.M8500_8700.SplitData.node5919 := by
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
  · exact treeEq5920

def B5929 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq5929 : B5929.tree = HexagonCover.NBand.M8500_8700.SplitData.node5929 := by
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

def B5928 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5929, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq5928 : B5928.tree = HexagonCover.NBand.M8500_8700.SplitData.node5928 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5929
  · rfl

def B5927 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5928]
theorem treeEq5927 : B5927.tree = HexagonCover.NBand.M8500_8700.SplitData.node5927 := by
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
  · exact treeEq5928

def B5926 : Block := .branch 172 ![1237940334433285454251950465, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B5927, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq5926 : B5926.tree = HexagonCover.NBand.M8500_8700.SplitData.node5926 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5927
  · rfl
  · rfl
  · rfl

def B5925 : Block := .branch 159 ![10385863224580237562438081063158145, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 989).pointIds 989), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B5926]
theorem treeEq5925 : B5925.tree = HexagonCover.NBand.M8500_8700.SplitData.node5925 := by
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
  · exact treeEq5926

def B5933 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq5933 : B5933.tree = HexagonCover.NBand.M8500_8700.SplitData.node5933 := by
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

def B5932 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5933, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq5932 : B5932.tree = HexagonCover.NBand.M8500_8700.SplitData.node5932 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5933
  · rfl

def B5931 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5932]
theorem treeEq5931 : B5931.tree = HexagonCover.NBand.M8500_8700.SplitData.node5931 := by
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
  · exact treeEq5932

def B5930 : Block := .branch 172 ![1237940334433285454251950465, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B5931, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq5930 : B5930.tree = HexagonCover.NBand.M8500_8700.SplitData.node5930 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5931
  · rfl
  · rfl
  · rfl

def B5924 : Block := .branch 113 ![1269507510582305377088404717953, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B5925, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B5930]
theorem treeEq5924 : B5924.tree = HexagonCover.NBand.M8500_8700.SplitData.node5924 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5925
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5930

def B5918 : Block := .branch 112 ![1269507510582305377088404717953, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B5919, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B5924]
theorem treeEq5918 : B5918.tree = HexagonCover.NBand.M8500_8700.SplitData.node5918 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5919
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5924

def B5935 : Block := .branch 168 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 990).pointIds 990), (.leaf 1 (Common.fact 978).pointIds 978), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq5935 : B5935.tree = HexagonCover.NBand.M8500_8700.SplitData.node5935 := by
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

def B5934 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5935, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq5934 : B5934.tree = HexagonCover.NBand.M8500_8700.SplitData.node5934 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5935
  · rfl

def B5917 : Block := .branch 109 ![1269507510582305377088404717953, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B5918, (.leaf 5 (Common.fact 294).pointIds 294), B5934]
theorem treeEq5917 : B5917.tree = HexagonCover.NBand.M8500_8700.SplitData.node5917 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5918
  · rfl
  · exact treeEq5934

theorem accepted5917 : B5917.accepted = true := by decide +kernel
theorem checked5917 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5917 (maskNeeds ![1269507510582305377088404717953, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq5917]
  exact B5917.sound accepted5917
#print axioms checked5917

def B5961 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq5961 : B5961.tree = HexagonCover.NBand.M8500_8700.SplitData.node5961 := by
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

def B5960 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5961, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq5960 : B5960.tree = HexagonCover.NBand.M8500_8700.SplitData.node5960 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5961
  · rfl

def B5959 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5960]
theorem treeEq5959 : B5959.tree = HexagonCover.NBand.M8500_8700.SplitData.node5959 := by
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
  · exact treeEq5960

def B5958 : Block := .branch 172 ![1237940334433285454251950465, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B5959, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq5958 : B5958.tree = HexagonCover.NBand.M8500_8700.SplitData.node5958 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5959
  · rfl
  · rfl
  · rfl

def B5957 : Block := .branch 159 ![5193565747377621746121104578052481, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 992).pointIds 992), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B5958]
theorem treeEq5957 : B5957.tree = HexagonCover.NBand.M8500_8700.SplitData.node5957 := by
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
  · exact treeEq5958

def B5967 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq5967 : B5967.tree = HexagonCover.NBand.M8500_8700.SplitData.node5967 := by
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

def B5966 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5967, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq5966 : B5966.tree = HexagonCover.NBand.M8500_8700.SplitData.node5966 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5967
  · rfl

def B5965 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5966]
theorem treeEq5965 : B5965.tree = HexagonCover.NBand.M8500_8700.SplitData.node5965 := by
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
  · exact treeEq5966

def B5964 : Block := .branch 172 ![1237940334433285454251950465, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B5965, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq5964 : B5964.tree = HexagonCover.NBand.M8500_8700.SplitData.node5964 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5965
  · rfl
  · rfl
  · rfl

def B5963 : Block := .branch 159 ![10385862605912449374651600907272577, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 993).pointIds 993), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B5964]
theorem treeEq5963 : B5963.tree = HexagonCover.NBand.M8500_8700.SplitData.node5963 := by
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
  · exact treeEq5964

def B5971 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq5971 : B5971.tree = HexagonCover.NBand.M8500_8700.SplitData.node5971 := by
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

def B5970 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5971, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq5970 : B5970.tree = HexagonCover.NBand.M8500_8700.SplitData.node5970 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5971
  · rfl

def B5969 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5970]
theorem treeEq5969 : B5969.tree = HexagonCover.NBand.M8500_8700.SplitData.node5969 := by
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
  · exact treeEq5970

def B5968 : Block := .branch 172 ![1237940334433285454251950465, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B5969, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq5968 : B5968.tree = HexagonCover.NBand.M8500_8700.SplitData.node5968 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5969
  · rfl
  · rfl
  · rfl

def B5962 : Block := .branch 113 ![1268888842794117590608248832385, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B5963, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B5968]
theorem treeEq5962 : B5962.tree = HexagonCover.NBand.M8500_8700.SplitData.node5962 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5963
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5968

def B5956 : Block := .branch 112 ![1268888842794117590608248832385, 151115729774546960516610, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B5957, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B5962]
theorem treeEq5956 : B5956.tree = HexagonCover.NBand.M8500_8700.SplitData.node5956 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5957
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5962

def B5973 : Block := .branch 168 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 990).pointIds 990), (.leaf 1 (Common.fact 978).pointIds 978), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq5973 : B5973.tree = HexagonCover.NBand.M8500_8700.SplitData.node5973 := by
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

def B5972 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5973, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq5972 : B5972.tree = HexagonCover.NBand.M8500_8700.SplitData.node5972 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5973
  · rfl

def B5955 : Block := .branch 109 ![1268888842794117590608248832385, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B5956, (.leaf 5 (Common.fact 294).pointIds 294), B5972]
theorem treeEq5955 : B5955.tree = HexagonCover.NBand.M8500_8700.SplitData.node5955 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5956
  · rfl
  · exact treeEq5972

theorem accepted5955 : B5955.accepted = true := by decide +kernel
theorem checked5955 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5955 (maskNeeds ![1268888842794117590608248832385, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq5955]
  exact B5955.sound accepted5955
#print axioms checked5955

end HexagonCover.NBand.M8500_8700.SplitTree.Run0082
