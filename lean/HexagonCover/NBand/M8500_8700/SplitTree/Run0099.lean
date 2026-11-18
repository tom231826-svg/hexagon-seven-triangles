import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0098
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0099
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B7027 : Block := .branch 169 ![618970019642690137449562497, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 1145).pointIds 1145)]
theorem treeEq7027 : B7027.tree = HexagonCover.NBand.M8500_8700.SplitData.node7027 := by
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

def B7026 : Block := .branch 170 ![1856910058928070412348686721, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 1165).pointIds 1165), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B7027, (.leaf 6 (Common.fact 1142).pointIds 1142)]
theorem treeEq7026 : B7026.tree = HexagonCover.NBand.M8500_8700.SplitData.node7026 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7027
  · rfl

def B7025 : Block := .branch 174 ![1856910059504531164652110209, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 1163).pointIds 1163), B7026, (.leaf 2 (Common.fact 1164).pointIds 1164), (.leaf 3 (Common.fact 1148).pointIds 1148), (.leaf 4 (Common.fact 1130).pointIds 1130), (.leaf 5 (Common.fact 1080).pointIds 1080), (.leaf 6 (Common.fact 1131).pointIds 1131)]
theorem treeEq7025 : B7025.tree = HexagonCover.NBand.M8500_8700.SplitData.node7025 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7026
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7024 : Block := .branch 171 ![1856910059504531164652110209, 151115727451828646839810, 37778931863506917529604, 5986310706507378352962451531130923777185886783954952, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 1161).pointIds 1161), (.leaf 2 (Common.fact 1162).pointIds 1162), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B7025]
theorem treeEq7024 : B7024.tree = HexagonCover.NBand.M8500_8700.SplitData.node7024 := by
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
  · exact treeEq7025

def B7023 : Block := .branch 172 ![1856910059504531164652110209, 151115727451828646839810, 4873482210322023616354308, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 1159).pointIds 1159), (.leaf 2 (Common.fact 1160).pointIds 1160), B7024, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1126).pointIds 1126)]
theorem treeEq7023 : B7023.tree = HexagonCover.NBand.M8500_8700.SplitData.node7023 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7024
  · rfl
  · rfl
  · rfl

def B7031 : Block := .branch 161 ![385, 1538, 9709185488780540315179012, 158461160731807133703786749960, 98320, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 1170).pointIds 1170), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), (.leaf 6 (Common.fact 1171).pointIds 1171)]
theorem treeEq7031 : B7031.tree = HexagonCover.NBand.M8500_8700.SplitData.node7031 := by
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
  · rfl

def B7030 : Block := .branch 171 ![1237940039285380274899124609, 151115727451828646839810, 9709185488780540315179012, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 1161).pointIds 1161), (.leaf 2 (Common.fact 1162).pointIds 1162), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B7031]
theorem treeEq7030 : B7030.tree = HexagonCover.NBand.M8500_8700.SplitData.node7030 := by
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
  · exact treeEq7031

def B7029 : Block := .branch 172 ![1237940039285380274899124609, 151115727451828646839810, 9709185488780540315179012, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 1159).pointIds 1159), (.leaf 2 (Common.fact 1169).pointIds 1169), B7030, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1126).pointIds 1126)]
theorem treeEq7029 : B7029.tree = HexagonCover.NBand.M8500_8700.SplitData.node7029 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7030
  · rfl
  · rfl
  · rfl

def B7035 : Block := .branch 169 ![618970019642690137449562497, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 1145).pointIds 1145)]
theorem treeEq7035 : B7035.tree = HexagonCover.NBand.M8500_8700.SplitData.node7035 := by
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

def B7034 : Block := .branch 170 ![1856910058928070412348686721, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 1165).pointIds 1165), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B7035, (.leaf 6 (Common.fact 1142).pointIds 1142)]
theorem treeEq7034 : B7034.tree = HexagonCover.NBand.M8500_8700.SplitData.node7034 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7035
  · rfl

def B7033 : Block := .branch 174 ![1856910059504531164652110209, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 1163).pointIds 1163), B7034, (.leaf 2 (Common.fact 1164).pointIds 1164), (.leaf 3 (Common.fact 1148).pointIds 1148), (.leaf 4 (Common.fact 1130).pointIds 1130), (.leaf 5 (Common.fact 1080).pointIds 1080), (.leaf 6 (Common.fact 1131).pointIds 1131)]
theorem treeEq7033 : B7033.tree = HexagonCover.NBand.M8500_8700.SplitData.node7033 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7034
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7032 : Block := .branch 171 ![1856910059504531164652110209, 151115727451828646839810, 37778931863506917529604, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 1161).pointIds 1161), (.leaf 2 (Common.fact 1162).pointIds 1162), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B7033]
theorem treeEq7032 : B7032.tree = HexagonCover.NBand.M8500_8700.SplitData.node7032 := by
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
  · exact treeEq7033

def B7028 : Block := .branch 83 ![1856910059504531164652110209, 151115727451828646839810, 37778931863506917529604, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11972621413058360701098314529906526983827385570820160] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B7029, B7032, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq7028 : B7028.tree = HexagonCover.NBand.M8500_8700.SplitData.node7028 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7029
  · exact treeEq7032
  · rfl
  · rfl
  · rfl

def B7022 : Block := .branch 82 ![1856910059504531164652110209, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413058360701098314529906526983827385570820160] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B7023, B7028, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq7022 : B7022.tree = HexagonCover.NBand.M8500_8700.SplitData.node7022 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7023
  · exact treeEq7028
  · rfl
  · rfl
  · rfl

def B7021 : Block := .branch 51 ![1856910059504531164652110209, 1461501637330902918203684983832010541853323560450, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413058360701098314529906526983827385570820160] ![B7022, (.leaf 1 (Common.fact 1158).pointIds 1158), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), (.leaf 4 (Common.fact 209).pointIds 209), (.leaf 5 (Common.fact 210).pointIds 210), (.leaf 0 [] 0)]
theorem treeEq7021 : B7021.tree = HexagonCover.NBand.M8500_8700.SplitData.node7021 := by
  change Tree.branch (51 : Fin 175) _ = Tree.branch (51 : Fin 175) _
  apply congrArg (Tree.branch (51 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq7022
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7020 : Block := .branch 59 ![1856910058928070412348686721, 1461501637330902918203684983832010541853323560450, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413069249736839784560737354971265202153586752] ![B7021, (.leaf 1 (Common.fact 1157).pointIds 1157), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq7020 : B7020.tree = HexagonCover.NBand.M8500_8700.SplitData.node7020 := by
  change Tree.branch (59 : Fin 175) _ = Tree.branch (59 : Fin 175) _
  apply congrArg (Tree.branch (59 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq7021
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted7020 : B7020.accepted = true := by decide +kernel
theorem checked7020 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node7020 (maskNeeds ![1856910058928070412348686721, 1461501637330902918203684983832010541853323560450, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413069249736839784560737354971265202153586752]) := by
  rw [← treeEq7020]
  exact B7020.sound accepted7020
#print axioms checked7020

def Tip0033_0035 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0035 ![1237940039285380274899124609, 151115727522747146831362, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0098.checked0035
def Tip0033_7020 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node7020 ![1856910058928070412348686721, 1461501637330902918203684983832010541853323560450, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413069249736839784560737354971265202153586752] checked7020
def B7012 : Block := .branch 51 ![748288838313422294120287872290776191444112361128321, 23945242826029513411849172299223580994043348539934210, 6148, 24584, 98320, 393248, 0] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 1149).pointIds 1149), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), (.leaf 4 (Common.fact 209).pointIds 209), (.leaf 5 (Common.fact 210).pointIds 210), (.leaf 0 [] 0)]
theorem treeEq7012 : B7012.tree = HexagonCover.NBand.M8500_8700.SplitData.node7012 := by
  change Tree.branch (51 : Fin 175) _ = Tree.branch (51 : Fin 175) _
  apply congrArg (Tree.branch (51 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7011 : Block := .branch 174 ![748288838313422294120287872290776191444112361128321, 549755815426, 37778931933325905893380, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 1146).pointIds 1146), B7012, (.leaf 2 (Common.fact 1147).pointIds 1147), (.leaf 3 (Common.fact 1148).pointIds 1148), (.leaf 4 (Common.fact 1130).pointIds 1130), (.leaf 5 (Common.fact 1080).pointIds 1080), (.leaf 6 (Common.fact 1131).pointIds 1131)]
theorem treeEq7011 : B7011.tree = HexagonCover.NBand.M8500_8700.SplitData.node7011 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7012
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7010 : Block := .branch 169 ![1237940039285380274899124609, 151115727452378402653698, 37778931933325905893380, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 14965776766312044560667477927645982992854494297456704] ![B7011, (.leaf 1 (Common.fact 1143).pointIds 1143), (.leaf 2 (Common.fact 1144).pointIds 1144), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 1145).pointIds 1145)]
theorem treeEq7010 : B7010.tree = HexagonCover.NBand.M8500_8700.SplitData.node7010 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq7011
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7009 : Block := .branch 170 ![1237940039285380274899124609, 151115727452378402653698, 37778931933325905893380, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 1140).pointIds 1140), (.leaf 2 (Common.fact 1141).pointIds 1141), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B7010, (.leaf 6 (Common.fact 1142).pointIds 1142)]
theorem treeEq7009 : B7009.tree = HexagonCover.NBand.M8500_8700.SplitData.node7009 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7010
  · rfl

def B7008 : Block := .branch 171 ![1237940039285380274899124609, 151115727452378402653698, 37778931933325905893380, 5986310706507378352962451531130923777185886783954952, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 1138).pointIds 1138), (.leaf 2 (Common.fact 1139).pointIds 1139), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B7009]
theorem treeEq7008 : B7008.tree = HexagonCover.NBand.M8500_8700.SplitData.node7008 := by
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
  · exact treeEq7009

def B7007 : Block := .branch 172 ![1237940039285380274899124609, 151115727452378402653698, 37778931933325905893380, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 1136).pointIds 1136), (.leaf 2 (Common.fact 1137).pointIds 1137), B7008, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1126).pointIds 1126)]
theorem treeEq7007 : B7007.tree = HexagonCover.NBand.M8500_8700.SplitData.node7007 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7008
  · rfl
  · rfl
  · rfl

def B7006 : Block := .branch 173 ![1237940039285380274899124609, 151115727452378402653698, 37778931933325905893380, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 43598678261745240631244871577745057382464] ![(.leaf 0 (Common.fact 1119).pointIds 1119), (.leaf 1 (Common.fact 1133).pointIds 1133), (.leaf 2 (Common.fact 1134).pointIds 1134), (.leaf 3 (Common.fact 1135).pointIds 1135), (.leaf 4 (Common.fact 1123).pointIds 1123), (.leaf 5 (Common.fact 1074).pointIds 1074), B7007]
theorem treeEq7006 : B7006.tree = HexagonCover.NBand.M8500_8700.SplitData.node7006 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7007

def B0034 : Block := .branch 46 ![1237940039285380274899124609, 151115727452378402653698, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 202).pointIds 202), Tip0033_0035, B7006, (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), (.leaf 6 (Common.fact 206).pointIds 206)]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M8500_8700.SplitData.node0034 := by
  change Tree.branch (46 : Fin 175) _ = Tree.branch (46 : Fin 175) _
  apply congrArg (Tree.branch (46 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7006
  · rfl
  · rfl
  · rfl
  · rfl

def B7039 : Block := .branch 169 ![618970019642690137449562497, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 1145).pointIds 1145)]
theorem treeEq7039 : B7039.tree = HexagonCover.NBand.M8500_8700.SplitData.node7039 := by
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

def B7038 : Block := .branch 170 ![1856910058928070412348686721, 151115727451828646839810, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 1165).pointIds 1165), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B7039, (.leaf 6 (Common.fact 1142).pointIds 1142)]
theorem treeEq7038 : B7038.tree = HexagonCover.NBand.M8500_8700.SplitData.node7038 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7039
  · rfl

def B7037 : Block := .branch 171 ![1856910058928070412348686721, 151115727451828646839810, 37778931863506917529604, 5986310706507378352962451531130923777185886783954952, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 1161).pointIds 1161), (.leaf 2 (Common.fact 1162).pointIds 1162), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B7038]
theorem treeEq7037 : B7037.tree = HexagonCover.NBand.M8500_8700.SplitData.node7037 := by
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
  · exact treeEq7038

def B7036 : Block := .branch 172 ![1856910058928070412348686721, 151115727451828646839810, 37778931933875661707268, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 1159).pointIds 1159), (.leaf 2 (Common.fact 1172).pointIds 1172), B7037, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1126).pointIds 1126)]
theorem treeEq7036 : B7036.tree = HexagonCover.NBand.M8500_8700.SplitData.node7036 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7037
  · rfl
  · rfl
  · rfl

def B7019 : Block := .branch 46 ![1856910058928070412348686721, 1461501637330902918203684983832010471484579382786, 37778931863506917529604, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11972621413069249736839784560737354971265202153586752] ![(.leaf 0 (Common.fact 202).pointIds 202), Tip0033_7020, B7036, (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), (.leaf 6 (Common.fact 206).pointIds 206)]
theorem treeEq7019 : B7019.tree = HexagonCover.NBand.M8500_8700.SplitData.node7019 := by
  change Tree.branch (46 : Fin 175) _ = Tree.branch (46 : Fin 175) _
  apply congrArg (Tree.branch (46 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7036
  · rfl
  · rfl
  · rfl
  · rfl

def B7018 : Block := .branch 109 ![1856910058928070412348686721, 1461501637330902918203684983832010471484579382786, 37778931863506917529604, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11972621413069249736839784560737354971265202153586752] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B7019, (.leaf 5 (Common.fact 294).pointIds 294), (.leaf 6 (Common.fact 1156).pointIds 1156)]
theorem treeEq7018 : B7018.tree = HexagonCover.NBand.M8500_8700.SplitData.node7018 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7019
  · rfl
  · rfl

def B7017 : Block := .branch 68 ![1856910058928070412348686721, 1461501637330902918203684983832010471484579382786, 37778931863506917529604, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11972621413091027808322724622399010946140835319119936] ![B7018, (.leaf 1 (Common.fact 1155).pointIds 1155), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq7017 : B7017.tree = HexagonCover.NBand.M8500_8700.SplitData.node7017 := by
  change Tree.branch (68 : Fin 175) _ = Tree.branch (68 : Fin 175) _
  apply congrArg (Tree.branch (68 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq7018
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7016 : Block := .branch 78 ![1856910058928070412348686721, 1461501637330902918203684983832010471484579382786, 37778931863506917529604, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11972621413091027808322724622399010946140835319119936] ![B7017, (.leaf 1 (Common.fact 1154).pointIds 1154), (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq7016 : B7016.tree = HexagonCover.NBand.M8500_8700.SplitData.node7016 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq7017
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7015 : Block := .branch 89 ![1237940039285380274899124609, 1461501637330902918203684983832010471484579382786, 37778931863506917529604, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11972621413091027808322724622399010946140835319119936] ![B7016, (.leaf 1 (Common.fact 1153).pointIds 1153), (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq7015 : B7015.tree = HexagonCover.NBand.M8500_8700.SplitData.node7015 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq7016
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7014 : Block := .branch 160 ![1237940039285380274899124609, 151115727451828646839810, 37778931863506917529604, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11972621413091027808322724622399010946140835319119936] ![(.leaf 0 (Common.fact 392).pointIds 392), B7015, (.leaf 2 (Common.fact 1152).pointIds 1152), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 1124).pointIds 1124)]
theorem treeEq7014 : B7014.tree = HexagonCover.NBand.M8500_8700.SplitData.node7014 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7015
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7013 : Block := .branch 173 ![1237940039285380274899124609, 151115727451828646839810, 37778931863506917529604, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 76271102398138472787220449119435927060544] ![(.leaf 0 (Common.fact 1119).pointIds 1119), (.leaf 1 (Common.fact 1150).pointIds 1150), (.leaf 2 (Common.fact 1151).pointIds 1151), (.leaf 3 (Common.fact 1135).pointIds 1135), (.leaf 4 (Common.fact 1123).pointIds 1123), (.leaf 5 (Common.fact 1074).pointIds 1074), B7014]
theorem treeEq7013 : B7013.tree = HexagonCover.NBand.M8500_8700.SplitData.node7013 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7014

def B0033 : Block := .branch 39 ![1237940039285380274899124609, 151115727451828646839810, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 198).pointIds 198), B0034, B7013, (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 0 [] 0)]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M8500_8700.SplitData.node0033 := by
  change Tree.branch (39 : Fin 175) _ = Tree.branch (39 : Fin 175) _
  apply congrArg (Tree.branch (39 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0034
  · exact treeEq7013
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0033 : B0033.accepted = true := by decide +kernel
theorem checked0033 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0033 (maskNeeds ![1237940039285380274899124609, 151115727451828646839810, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq0033]
  exact B0033.sound accepted0033
#print axioms checked0033

def Tip0013_0033 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0033 ![1237940039285380274899124609, 151115727451828646839810, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] checked0033
def B0032 : Block := .branch 75 ![1237940039285380274899124609, 151115727451828646839810, 18446744073709557764, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), Tip0013_0033, (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), (.leaf 6 (Common.fact 197).pointIds 197)]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M8500_8700.SplitData.node0032 := by
  change Tree.branch (75 : Fin 175) _ = Tree.branch (75 : Fin 175) _
  apply congrArg (Tree.branch (75 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0031 : Block := .branch 90 ![385, 151115727451828646839810, 18446744073709557764, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B0032, (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M8500_8700.SplitData.node0031 := by
  change Tree.branch (90 : Fin 175) _ = Tree.branch (90 : Fin 175) _
  apply congrArg (Tree.branch (90 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0032
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0030 : Block := .branch 77 ![385, 1538, 18446744073709557764, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 180).pointIds 180), B0031, (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 183).pointIds 183), (.leaf 5 (Common.fact 184).pointIds 184), (.leaf 6 (Common.fact 185).pointIds 185)]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M8500_8700.SplitData.node0030 := by
  change Tree.branch (77 : Fin 175) _ = Tree.branch (77 : Fin 175) _
  apply congrArg (Tree.branch (77 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0031
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0029 : Block := .branch 120 ![385, 1538, 18446744073709557764, 237684487542793012780631875592, 1393796574908163946345982392040522594222096, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), B0030, (.leaf 5 (Common.fact 178).pointIds 178), (.leaf 6 (Common.fact 179).pointIds 179)]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M8500_8700.SplitData.node0029 := by
  change Tree.branch (120 : Fin 175) _ = Tree.branch (120 : Fin 175) _
  apply congrArg (Tree.branch (120 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0030
  · rfl
  · rfl

def B0028 : Block := .branch 130 ![385, 1538, 18446744073709557764, 237684487542793012780631875592, 1393796574908163946345982392040522594222096, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 168).pointIds 168), (.leaf 1 (Common.fact 169).pointIds 169), (.leaf 2 (Common.fact 170).pointIds 170), (.leaf 3 (Common.fact 171).pointIds 171), B0029, (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 173).pointIds 173)]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M8500_8700.SplitData.node0028 := by
  change Tree.branch (130 : Fin 175) _ = Tree.branch (130 : Fin 175) _
  apply congrArg (Tree.branch (130 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0029
  · rfl
  · rfl

def B0027 : Block := .branch 139 ![385, 1538, 18446744073709557764, 277298568799925181577403850760, 1393796574908163946345982392040522594222096, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 162).pointIds 162), (.leaf 1 (Common.fact 163).pointIds 163), (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), B0028, (.leaf 5 (Common.fact 166).pointIds 166), (.leaf 6 (Common.fact 167).pointIds 167)]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M8500_8700.SplitData.node0027 := by
  change Tree.branch (139 : Fin 175) _ = Tree.branch (139 : Fin 175) _
  apply congrArg (Tree.branch (139 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0028
  · rfl
  · rfl

def B0026 : Block := .branch 91 ![385, 1538, 18446744073709557764, 277298568799925181577403850760, 1393796574908163946345982392040522594222096, 393248, 11226643701663450043555079585443616680050752] ![B0027, (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), (.leaf 4 (Common.fact 159).pointIds 159), (.leaf 5 (Common.fact 160).pointIds 160), (.leaf 6 (Common.fact 161).pointIds 161)]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M8500_8700.SplitData.node0026 := by
  change Tree.branch (91 : Fin 175) _ = Tree.branch (91 : Fin 175) _
  apply congrArg (Tree.branch (91 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0027
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0025 : Block := .branch 143 ![385, 1538, 18446744073709557764, 277298568799925181577403850760, 1393796574908163946345982392040522594222096, 393248, 76271102398138472787220449119435927060544] ![(.leaf 0 (Common.fact 150).pointIds 150), (.leaf 1 (Common.fact 151).pointIds 151), (.leaf 2 (Common.fact 152).pointIds 152), (.leaf 3 (Common.fact 153).pointIds 153), (.leaf 4 (Common.fact 154).pointIds 154), (.leaf 5 (Common.fact 155).pointIds 155), B0026]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M8500_8700.SplitData.node0025 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0026

def B0024 : Block := .branch 140 ![385, 1538, 18446744073709557764, 277298568799925181577403850760, 98320, 393248, 76271102398138472787220449119435927060544] ![(.leaf 0 (Common.fact 144).pointIds 144), (.leaf 1 (Common.fact 145).pointIds 145), (.leaf 2 (Common.fact 146).pointIds 146), (.leaf 3 (Common.fact 147).pointIds 147), B0025, (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 149).pointIds 149)]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M8500_8700.SplitData.node0024 := by
  change Tree.branch (140 : Fin 175) _ = Tree.branch (140 : Fin 175) _
  apply congrArg (Tree.branch (140 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0025
  · rfl
  · rfl

def B0023 : Block := .branch 148 ![385, 1538, 18446744073709557764, 277298568799925181577403850760, 98320, 393248, 76271102398138472787220449119435927060544] ![(.leaf 0 (Common.fact 138).pointIds 138), (.leaf 1 (Common.fact 139).pointIds 139), (.leaf 2 (Common.fact 140).pointIds 140), (.leaf 3 (Common.fact 141).pointIds 141), B0024, (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 143).pointIds 143)]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M8500_8700.SplitData.node0023 := by
  change Tree.branch (148 : Fin 175) _ = Tree.branch (148 : Fin 175) _
  apply congrArg (Tree.branch (148 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0024
  · rfl
  · rfl

def B0022 : Block := .branch 125 ![604462909807314587353473, 1538, 18446744073709557764, 277298568799925181577403850760, 98320, 393248, 76228567102273355479287527293506956034112] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 136).pointIds 136), (.leaf 5 (Common.fact 137).pointIds 137), B0023]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M8500_8700.SplitData.node0022 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0023

def B0021 : Block := .branch 79 ![385, 216172782113785346, 18446744073709557764, 277298568799925181577403850760, 98320, 393248, 76228567102273355479287527293506956034112] ![B0022, (.leaf 1 (Common.fact 126).pointIds 126), (.leaf 2 (Common.fact 127).pointIds 127), (.leaf 3 (Common.fact 128).pointIds 128), (.leaf 4 (Common.fact 129).pointIds 129), (.leaf 5 (Common.fact 130).pointIds 130), (.leaf 6 (Common.fact 131).pointIds 131)]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M8500_8700.SplitData.node0021 := by
  change Tree.branch (79 : Fin 175) _ = Tree.branch (79 : Fin 175) _
  apply congrArg (Tree.branch (79 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0022
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0020 : Block := .branch 56 ![385, 144115188075857410, 18907912675552290412548, 277298568799925181577403850760, 98320, 393248, 76228567102273355479287527293506956034112] ![(.leaf 0 (Common.fact 120).pointIds 120), B0021, (.leaf 2 (Common.fact 121).pointIds 121), (.leaf 3 (Common.fact 122).pointIds 122), (.leaf 4 (Common.fact 123).pointIds 123), (.leaf 5 (Common.fact 124).pointIds 124), (.leaf 6 (Common.fact 125).pointIds 125)]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M8500_8700.SplitData.node0020 := by
  change Tree.branch (56 : Fin 175) _ = Tree.branch (56 : Fin 175) _
  apply congrArg (Tree.branch (56 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0021
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0019 : Block := .branch 74 ![385, 144115188075857410, 18446744073709557764, 277298568799925181577403850760, 98320, 393248, 76228567102273355479287527293506956034112] ![(.leaf 0 (Common.fact 114).pointIds 114), (.leaf 1 (Common.fact 115).pointIds 115), B0020, (.leaf 3 (Common.fact 116).pointIds 116), (.leaf 4 (Common.fact 117).pointIds 117), (.leaf 5 (Common.fact 118).pointIds 118), (.leaf 6 (Common.fact 119).pointIds 119)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M8500_8700.SplitData.node0019 := by
  change Tree.branch (74 : Fin 175) _ = Tree.branch (74 : Fin 175) _
  apply congrArg (Tree.branch (74 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl
  · rfl
  · rfl

def B0018 : Block := .branch 97 ![385, 144115188075857410, 18446744073709557764, 118842243771396506390315950088, 98320, 393248, 76228567102273355479287527293506956034112] ![(.leaf 0 (Common.fact 108).pointIds 108), (.leaf 1 (Common.fact 109).pointIds 109), (.leaf 2 (Common.fact 110).pointIds 110), B0019, (.leaf 4 (Common.fact 111).pointIds 111), (.leaf 5 (Common.fact 112).pointIds 112), (.leaf 6 (Common.fact 113).pointIds 113)]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M8500_8700.SplitData.node0018 := by
  change Tree.branch (97 : Fin 175) _ = Tree.branch (97 : Fin 175) _
  apply congrArg (Tree.branch (97 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0019
  · rfl
  · rfl
  · rfl

def B0017 : Block := .branch 147 ![385, 144115188075857410, 18446744073709557764, 118842243771396506390315950088, 98320, 393248, 76228567102273355479287527293506956034112] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), (.leaf 3 (Common.fact 105).pointIds 105), B0018, (.leaf 5 (Common.fact 106).pointIds 106), (.leaf 6 (Common.fact 107).pointIds 107)]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M8500_8700.SplitData.node0017 := by
  change Tree.branch (147 : Fin 175) _ = Tree.branch (147 : Fin 175) _
  apply congrArg (Tree.branch (147 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0018
  · rfl
  · rfl

def B0016 : Block := .branch 135 ![385, 144115188075857410, 18446744073709557764, 118842243771396506390315950088, 98320, 393248, 32672424136393232155975577542240624967744] ![(.leaf 0 (Common.fact 96).pointIds 96), (.leaf 1 (Common.fact 97).pointIds 97), (.leaf 2 (Common.fact 98).pointIds 98), (.leaf 3 (Common.fact 99).pointIds 99), (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), B0017]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M8500_8700.SplitData.node0016 := by
  change Tree.branch (135 : Fin 175) _ = Tree.branch (135 : Fin 175) _
  apply congrArg (Tree.branch (135 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0017

def B0015 : Block := .branch 69 ![385, 144255925564212738, 18446744073709557764, 118842243771396506390315950088, 98320, 393248, 32672424136393232155975577542240624967744] ![B0016, (.leaf 1 (Common.fact 90).pointIds 90), (.leaf 2 (Common.fact 91).pointIds 91), (.leaf 3 (Common.fact 92).pointIds 92), (.leaf 4 (Common.fact 93).pointIds 93), (.leaf 5 (Common.fact 94).pointIds 94), (.leaf 6 (Common.fact 95).pointIds 95)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M8500_8700.SplitData.node0015 := by
  change Tree.branch (69 : Fin 175) _ = Tree.branch (69 : Fin 175) _
  apply congrArg (Tree.branch (69 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0016
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0014 : Block := .branch 72 ![385, 144255925564212738, 18446744073709557764, 118842243771396506390315950088, 98320, 393248, 32672424136393232155975577542240624967744] ![(.leaf 0 (Common.fact 84).pointIds 84), (.leaf 1 (Common.fact 85).pointIds 85), B0015, (.leaf 3 (Common.fact 86).pointIds 86), (.leaf 4 (Common.fact 87).pointIds 87), (.leaf 5 (Common.fact 88).pointIds 88), (.leaf 6 (Common.fact 89).pointIds 89)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M8500_8700.SplitData.node0014 := by
  change Tree.branch (72 : Fin 175) _ = Tree.branch (72 : Fin 175) _
  apply congrArg (Tree.branch (72 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0015
  · rfl
  · rfl
  · rfl
  · rfl

def B0013 : Block := .branch 96 ![385, 144255925564212738, 18446744073709557764, 39614081257132168796771999752, 98320, 393248, 32672424136393232155975577542240624967744] ![(.leaf 0 (Common.fact 78).pointIds 78), (.leaf 1 (Common.fact 79).pointIds 79), (.leaf 2 (Common.fact 80).pointIds 80), B0014, (.leaf 4 (Common.fact 81).pointIds 81), (.leaf 5 (Common.fact 82).pointIds 82), (.leaf 6 (Common.fact 83).pointIds 83)]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M8500_8700.SplitData.node0013 := by
  change Tree.branch (96 : Fin 175) _ = Tree.branch (96 : Fin 175) _
  apply congrArg (Tree.branch (96 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0014
  · rfl
  · rfl
  · rfl

theorem accepted0013 : B0013.accepted = true := by decide +kernel
theorem checked0013 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0013 (maskNeeds ![385, 144255925564212738, 18446744073709557764, 39614081257132168796771999752, 98320, 393248, 32672424136393232155975577542240624967744]) := by
  rw [← treeEq0013]
  exact B0013.sound accepted0013
#print axioms checked0013

def Tip0000_0013 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0013 ![385, 144255925564212738, 18446744073709557764, 39614081257132168796771999752, 98320, 393248, 32672424136393232155975577542240624967744] checked0013
def B0012 : Block := .branch 106 ![385, 144255925564212738, 18446744073709557764, 39614081257132168796771999752, 98320, 393248, 32672424136393232155975577542240624967744] ![(.leaf 0 (Common.fact 72).pointIds 72), (.leaf 1 (Common.fact 73).pointIds 73), (.leaf 2 (Common.fact 74).pointIds 74), Tip0000_0013, (.leaf 4 (Common.fact 75).pointIds 75), (.leaf 5 (Common.fact 76).pointIds 76), (.leaf 6 (Common.fact 77).pointIds 77)]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M8500_8700.SplitData.node0012 := by
  change Tree.branch (106 : Fin 175) _ = Tree.branch (106 : Fin 175) _
  apply congrArg (Tree.branch (106 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0011 : Block := .branch 134 ![385, 144255925564212738, 18446744073709557764, 39614081257132168796771999752, 98320, 393248, 10894352653453170494319602666607459434560] ![(.leaf 0 (Common.fact 66).pointIds 66), (.leaf 1 (Common.fact 67).pointIds 67), (.leaf 2 (Common.fact 68).pointIds 68), (.leaf 3 (Common.fact 69).pointIds 69), (.leaf 4 (Common.fact 70).pointIds 70), (.leaf 5 (Common.fact 71).pointIds 71), B0012]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M8500_8700.SplitData.node0011 := by
  change Tree.branch (134 : Fin 175) _ = Tree.branch (134 : Fin 175) _
  apply congrArg (Tree.branch (134 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0012

def B0010 : Block := .branch 57 ![385, 140737488356866, 18446744073709557764, 39614081257132168796771999752, 98320, 393248, 10894352653453170494319602666607459434560] ![(.leaf 0 (Common.fact 60).pointIds 60), B0011, (.leaf 2 (Common.fact 61).pointIds 61), (.leaf 3 (Common.fact 62).pointIds 62), (.leaf 4 (Common.fact 63).pointIds 63), (.leaf 5 (Common.fact 64).pointIds 64), (.leaf 6 (Common.fact 65).pointIds 65)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M8500_8700.SplitData.node0010 := by
  change Tree.branch (57 : Fin 175) _ = Tree.branch (57 : Fin 175) _
  apply congrArg (Tree.branch (57 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 47 ![385, 1538, 18446744073709557764, 39614081257132168796771999752, 98320, 393248, 10894352653453170494319602666607459434560] ![(.leaf 0 (Common.fact 54).pointIds 54), B0010, (.leaf 2 (Common.fact 55).pointIds 55), (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M8500_8700.SplitData.node0009 := by
  change Tree.branch (47 : Fin 175) _ = Tree.branch (47 : Fin 175) _
  apply congrArg (Tree.branch (47 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 95 ![385, 1538, 18446744073709557764, 24584, 98320, 393248, 10894352653453170494319602666607459434560] ![(.leaf 0 (Common.fact 48).pointIds 48), (.leaf 1 (Common.fact 49).pointIds 49), (.leaf 2 (Common.fact 50).pointIds 50), B0009, (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M8500_8700.SplitData.node0008 := by
  change Tree.branch (95 : Fin 175) _ = Tree.branch (95 : Fin 175) _
  apply congrArg (Tree.branch (95 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 64 ![385, 1538, 6148, 24584, 98320, 393248, 10894352653453170494319602666607459434560] ![(.leaf 0 (Common.fact 42).pointIds 42), (.leaf 1 (Common.fact 43).pointIds 43), B0008, (.leaf 3 (Common.fact 44).pointIds 44), (.leaf 4 (Common.fact 45).pointIds 45), (.leaf 5 (Common.fact 46).pointIds 46), (.leaf 6 (Common.fact 47).pointIds 47)]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M8500_8700.SplitData.node0007 := by
  change Tree.branch (64 : Fin 175) _ = Tree.branch (64 : Fin 175) _
  apply congrArg (Tree.branch (64 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0008
  · rfl
  · rfl
  · rfl
  · rfl

def B0006 : Block := .branch 105 ![385, 1538, 6148, 24584, 98320, 393248, 10894352653453170494319602666607459434560] ![(.leaf 0 (Common.fact 36).pointIds 36), (.leaf 1 (Common.fact 37).pointIds 37), (.leaf 2 (Common.fact 38).pointIds 38), B0007, (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M8500_8700.SplitData.node0006 := by
  change Tree.branch (105 : Fin 175) _ = Tree.branch (105 : Fin 175) _
  apply congrArg (Tree.branch (105 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0007
  · rfl
  · rfl
  · rfl

def B0005 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), (.leaf 2 (Common.fact 32).pointIds 32), (.leaf 3 (Common.fact 33).pointIds 33), (.leaf 4 (Common.fact 34).pointIds 34), (.leaf 5 (Common.fact 35).pointIds 35), B0006]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M8500_8700.SplitData.node0005 := by
  change Tree.branch (133 : Fin 175) _ = Tree.branch (133 : Fin 175) _
  apply congrArg (Tree.branch (133 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0006

def B0004 : Block := .branch 48 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 24).pointIds 24), B0005, (.leaf 2 (Common.fact 25).pointIds 25), (.leaf 3 (Common.fact 26).pointIds 26), (.leaf 4 (Common.fact 27).pointIds 27), (.leaf 5 (Common.fact 28).pointIds 28), (.leaf 6 (Common.fact 29).pointIds 29)]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M8500_8700.SplitData.node0004 := by
  change Tree.branch (48 : Fin 175) _ = Tree.branch (48 : Fin 175) _
  apply congrArg (Tree.branch (48 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0005
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0003 : Block := .branch 49 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 18).pointIds 18), B0004, (.leaf 2 (Common.fact 19).pointIds 19), (.leaf 3 (Common.fact 20).pointIds 20), (.leaf 4 (Common.fact 21).pointIds 21), (.leaf 5 (Common.fact 22).pointIds 22), (.leaf 6 (Common.fact 23).pointIds 23)]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M8500_8700.SplitData.node0003 := by
  change Tree.branch (49 : Fin 175) _ = Tree.branch (49 : Fin 175) _
  apply congrArg (Tree.branch (49 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0004
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0002 : Block := .branch 53 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), B0003, (.leaf 3 (Common.fact 14).pointIds 14), (.leaf 4 (Common.fact 15).pointIds 15), (.leaf 5 (Common.fact 16).pointIds 16), (.leaf 6 (Common.fact 17).pointIds 17)]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M8500_8700.SplitData.node0002 := by
  change Tree.branch (53 : Fin 175) _ = Tree.branch (53 : Fin 175) _
  apply congrArg (Tree.branch (53 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0003
  · rfl
  · rfl
  · rfl
  · rfl

def B0001 : Block := .branch 62 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), B0002, (.leaf 3 (Common.fact 8).pointIds 8), (.leaf 4 (Common.fact 9).pointIds 9), (.leaf 5 (Common.fact 10).pointIds 10), (.leaf 6 (Common.fact 11).pointIds 11)]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M8500_8700.SplitData.node0001 := by
  change Tree.branch (62 : Fin 175) _ = Tree.branch (62 : Fin 175) _
  apply congrArg (Tree.branch (62 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0002
  · rfl
  · rfl
  · rfl
  · rfl

def B0000 : Block := .branch 122 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M8500_8700.SplitData.node0000 := by
  change Tree.branch (122 : Fin 175) _ = Tree.branch (122 : Fin 175) _
  apply congrArg (Tree.branch (122 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0001

theorem accepted0000 : B0000.accepted = true := by decide +kernel
theorem checked0000 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M8500_8700.SplitTree.Run0099
