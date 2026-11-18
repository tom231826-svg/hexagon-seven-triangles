import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0011
import HexagonCover.NBand.M8500_8700.SplitTree.Run0013
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0014
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0883_0888 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0888 ![1237940335011998006369059201, 377789318630121372911106, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0013.checked0888
def B1058 : Block := .branch 160 ![385, 377789318630121372911106, 357842042605930235713034244, 24584, 98320, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 884).pointIds 884), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq1058 : B1058.tree = HexagonCover.NBand.M8500_8700.SplitData.node1058 := by
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
  · rfl

def B1057 : Block := .branch 161 ![385, 377789318630121372911106, 357842042605930235713034244, 158461160731807133703786749960, 98320, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 856).pointIds 856), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B1058]
theorem treeEq1057 : B1057.tree = HexagonCover.NBand.M8500_8700.SplitData.node1057 := by
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
  · exact treeEq1058

def B0887 : Block := .branch 88 ![1237940335011998006369059201, 377789318630121372911106, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), Tip0883_0888, B1057, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq0887 : B0887.tree = HexagonCover.NBand.M8500_8700.SplitData.node0887 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1057
  · rfl
  · rfl
  · rfl
  · rfl

def B1061 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1061 : B1061.tree = HexagonCover.NBand.M8500_8700.SplitData.node1061 := by
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

def B1060 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1061, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1060 : B1060.tree = HexagonCover.NBand.M8500_8700.SplitData.node1060 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1061
  · rfl

def B1059 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158538531984262469970967945224, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1060]
theorem treeEq1059 : B1059.tree = HexagonCover.NBand.M8500_8700.SplitData.node1059 := by
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
  · exact treeEq1060

def B0886 : Block := .branch 86 ![1237940335011998006369059201, 377789318630121372911106, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B0887, B1059, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq0886 : B0886.tree = HexagonCover.NBand.M8500_8700.SplitData.node0886 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0887
  · exact treeEq1059
  · rfl
  · rfl
  · rfl

def B1064 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1064 : B1064.tree = HexagonCover.NBand.M8500_8700.SplitData.node1064 := by
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

def B1063 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1064, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1063 : B1063.tree = HexagonCover.NBand.M8500_8700.SplitData.node1063 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1064
  · rfl

def B1062 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158499846358034801837377347592, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1063]
theorem treeEq1062 : B1062.tree = HexagonCover.NBand.M8500_8700.SplitData.node1062 := by
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
  · exact treeEq1063

def B0885 : Block := .branch 85 ![1237940335011998006369059201, 377789318630121372911106, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B0886, B1062, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq0885 : B0885.tree = HexagonCover.NBand.M8500_8700.SplitData.node0885 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0886
  · exact treeEq1062
  · rfl
  · rfl
  · rfl

def B1067 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1067 : B1067.tree = HexagonCover.NBand.M8500_8700.SplitData.node1067 := by
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

def B1066 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1067, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1066 : B1066.tree = HexagonCover.NBand.M8500_8700.SplitData.node1066 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1067
  · rfl

def B1065 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158480503544920967770582048776, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 863).pointIds 863), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1066]
theorem treeEq1065 : B1065.tree = HexagonCover.NBand.M8500_8700.SplitData.node1065 := by
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
  · exact treeEq1066

def B0884 : Block := .branch 84 ![1237940335011998006369059201, 377789318630121372911106, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B0885, B1065, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq0884 : B0884.tree = HexagonCover.NBand.M8500_8700.SplitData.node0884 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0885
  · exact treeEq1065
  · rfl
  · rfl
  · rfl

def B1070 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1070 : B1070.tree = HexagonCover.NBand.M8500_8700.SplitData.node1070 := by
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

def B1069 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1070, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1069 : B1069.tree = HexagonCover.NBand.M8500_8700.SplitData.node1069 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1070
  · rfl

def B1068 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1069]
theorem treeEq1068 : B1068.tree = HexagonCover.NBand.M8500_8700.SplitData.node1068 := by
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
  · exact treeEq1069

def B0883 : Block := .branch 83 ![1237940335011998006369059201, 377789318630121372911106, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B0884, B1068, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq0883 : B0883.tree = HexagonCover.NBand.M8500_8700.SplitData.node0883 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0884
  · exact treeEq1068
  · rfl
  · rfl
  · rfl

theorem accepted0883 : B0883.accepted = true := by decide +kernel
theorem checked0883 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0883 (maskNeeds ![1237940335011998006369059201, 377789318630121372911106, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq0883]
  exact B0883.sound accepted0883
#print axioms checked0883

def Tip0793_0798 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0798 ![1237940335011998006369059201, 377789318630121372911106, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0011.checked0798
def Tip0793_0883 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0883 ![1237940335011998006369059201, 377789318630121372911106, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] checked0883
def B0873 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0873 : B0873.tree = HexagonCover.NBand.M8500_8700.SplitData.node0873 := by
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

def B0872 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0873, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0872 : B0872.tree = HexagonCover.NBand.M8500_8700.SplitData.node0872 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0873
  · rfl

def B0871 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0872]
theorem treeEq0871 : B0871.tree = HexagonCover.NBand.M8500_8700.SplitData.node0871 := by
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
  · exact treeEq0872

def B0797 : Block := .branch 86 ![1237940335011998006369059201, 377789318630121372911106, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), Tip0793_0798, B0871, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq0797 : B0797.tree = HexagonCover.NBand.M8500_8700.SplitData.node0797 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0871
  · rfl
  · rfl
  · rfl

def B0876 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0876 : B0876.tree = HexagonCover.NBand.M8500_8700.SplitData.node0876 := by
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

def B0875 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0876, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0875 : B0875.tree = HexagonCover.NBand.M8500_8700.SplitData.node0875 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0876
  · rfl

def B0874 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 882).pointIds 882), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0875]
theorem treeEq0874 : B0874.tree = HexagonCover.NBand.M8500_8700.SplitData.node0874 := by
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
  · exact treeEq0875

def B0796 : Block := .branch 85 ![1237940335011998006369059201, 377789318630121372911106, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B0797, B0874, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq0796 : B0796.tree = HexagonCover.NBand.M8500_8700.SplitData.node0796 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0797
  · exact treeEq0874
  · rfl
  · rfl
  · rfl

def B0879 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0879 : B0879.tree = HexagonCover.NBand.M8500_8700.SplitData.node0879 := by
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

def B0878 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0879, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0878 : B0878.tree = HexagonCover.NBand.M8500_8700.SplitData.node0878 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0879
  · rfl

def B0877 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0878]
theorem treeEq0877 : B0877.tree = HexagonCover.NBand.M8500_8700.SplitData.node0877 := by
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
  · exact treeEq0878

def B0795 : Block := .branch 84 ![1237940335011998006369059201, 377789318630121372911106, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B0796, B0877, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq0795 : B0795.tree = HexagonCover.NBand.M8500_8700.SplitData.node0795 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0796
  · exact treeEq0877
  · rfl
  · rfl
  · rfl

def B0882 : Block := .branch 169 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0882 : B0882.tree = HexagonCover.NBand.M8500_8700.SplitData.node0882 := by
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

def B0881 : Block := .branch 170 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B0882, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq0881 : B0881.tree = HexagonCover.NBand.M8500_8700.SplitData.node0881 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0882
  · rfl

def B0880 : Block := .branch 171 ![1237940335011998006369059201, 377789318630121372911106, 37778931862957161715716, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 870).pointIds 870), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0881]
theorem treeEq0880 : B0880.tree = HexagonCover.NBand.M8500_8700.SplitData.node0880 := by
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
  · exact treeEq0881

def B0794 : Block := .branch 83 ![1237940335011998006369059201, 377789318630121372911106, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B0795, B0880, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq0794 : B0794.tree = HexagonCover.NBand.M8500_8700.SplitData.node0794 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0795
  · exact treeEq0880
  · rfl
  · rfl
  · rfl

def B0793 : Block := .branch 82 ![1237940335011998006369059201, 377789318630121372911106, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B0794, Tip0793_0883, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq0793 : B0793.tree = HexagonCover.NBand.M8500_8700.SplitData.node0793 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0794
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0793 : B0793.accepted = true := by decide +kernel
theorem checked0793 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0793 (maskNeeds ![1237940335011998006369059201, 377789318630121372911106, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq0793]
  exact B0793.sound accepted0793
#print axioms checked0793

def B1097 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq1097 : B1097.tree = HexagonCover.NBand.M8500_8700.SplitData.node1097 := by
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

def B1096 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1097, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq1096 : B1096.tree = HexagonCover.NBand.M8500_8700.SplitData.node1096 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1097
  · rfl

def B1095 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1096]
theorem treeEq1095 : B1095.tree = HexagonCover.NBand.M8500_8700.SplitData.node1095 := by
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
  · exact treeEq1096

def B1094 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1095, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq1094 : B1094.tree = HexagonCover.NBand.M8500_8700.SplitData.node1094 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1095
  · rfl
  · rfl
  · rfl

def B1093 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B1094]
theorem treeEq1093 : B1093.tree = HexagonCover.NBand.M8500_8700.SplitData.node1093 := by
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
  · exact treeEq1094

def B1099 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq1099 : B1099.tree = HexagonCover.NBand.M8500_8700.SplitData.node1099 := by
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

def B1098 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1099, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq1098 : B1098.tree = HexagonCover.NBand.M8500_8700.SplitData.node1098 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1099
  · rfl
  · rfl
  · rfl

def B1092 : Block := .branch 144 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B1093, B1098]
theorem treeEq1092 : B1092.tree = HexagonCover.NBand.M8500_8700.SplitData.node1092 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1093
  · exact treeEq1098

def B1105 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq1105 : B1105.tree = HexagonCover.NBand.M8500_8700.SplitData.node1105 := by
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

def B1104 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1105, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1104 : B1104.tree = HexagonCover.NBand.M8500_8700.SplitData.node1104 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1105
  · rfl

def B1103 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1104]
theorem treeEq1103 : B1103.tree = HexagonCover.NBand.M8500_8700.SplitData.node1103 := by
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
  · exact treeEq1104

def B1102 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1103, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq1102 : B1102.tree = HexagonCover.NBand.M8500_8700.SplitData.node1102 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1103
  · rfl
  · rfl
  · rfl

def B1101 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1102]
theorem treeEq1101 : B1101.tree = HexagonCover.NBand.M8500_8700.SplitData.node1101 := by
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
  · exact treeEq1102

def B1100 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1101, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq1100 : B1100.tree = HexagonCover.NBand.M8500_8700.SplitData.node1100 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1101
  · rfl

def B1091 : Block := .branch 142 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B1092, (.leaf 5 (Common.fact 339).pointIds 339), B1100]
theorem treeEq1091 : B1091.tree = HexagonCover.NBand.M8500_8700.SplitData.node1091 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1092
  · rfl
  · exact treeEq1100

theorem accepted1091 : B1091.accepted = true := by decide +kernel
theorem checked1091 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1091 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq1091]
  exact B1091.sound accepted1091
#print axioms checked1091

def Tip1088_1091 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1091 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] checked1091
def B1110 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1110 : B1110.tree = HexagonCover.NBand.M8500_8700.SplitData.node1110 := by
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

def B1109 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1110, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1109 : B1109.tree = HexagonCover.NBand.M8500_8700.SplitData.node1109 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1110
  · rfl

def B1108 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B1109]
theorem treeEq1108 : B1108.tree = HexagonCover.NBand.M8500_8700.SplitData.node1108 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1109

def B1107 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B1108, (.leaf 0 [] 0)]
theorem treeEq1107 : B1107.tree = HexagonCover.NBand.M8500_8700.SplitData.node1107 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1108
  · rfl

def B1106 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B1107, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1106 : B1106.tree = HexagonCover.NBand.M8500_8700.SplitData.node1106 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1107
  · rfl

def B1090 : Block := .branch 138 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip1088_1091, B1106, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq1090 : B1090.tree = HexagonCover.NBand.M8500_8700.SplitData.node1090 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1106
  · rfl
  · rfl

def B1116 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq1116 : B1116.tree = HexagonCover.NBand.M8500_8700.SplitData.node1116 := by
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

def B1115 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1116, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq1115 : B1115.tree = HexagonCover.NBand.M8500_8700.SplitData.node1115 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1116
  · rfl

def B1114 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1115]
theorem treeEq1114 : B1114.tree = HexagonCover.NBand.M8500_8700.SplitData.node1114 := by
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
  · exact treeEq1115

def B1113 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1114, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq1113 : B1113.tree = HexagonCover.NBand.M8500_8700.SplitData.node1113 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1114
  · rfl
  · rfl
  · rfl

def B1112 : Block := .branch 168 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B1113]
theorem treeEq1112 : B1112.tree = HexagonCover.NBand.M8500_8700.SplitData.node1112 := by
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
  · exact treeEq1113

def B1111 : Block := .branch 152 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B1112, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq1111 : B1111.tree = HexagonCover.NBand.M8500_8700.SplitData.node1111 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1112
  · rfl

def B1089 : Block := .branch 132 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1090, (.leaf 5 (Common.fact 329).pointIds 329), B1111]
theorem treeEq1089 : B1089.tree = HexagonCover.NBand.M8500_8700.SplitData.node1089 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1090
  · rfl
  · exact treeEq1111

def B1121 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1121 : B1121.tree = HexagonCover.NBand.M8500_8700.SplitData.node1121 := by
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

def B1120 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1121, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1120 : B1120.tree = HexagonCover.NBand.M8500_8700.SplitData.node1120 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1121
  · rfl

def B1119 : Block := .branch 163 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B1120]
theorem treeEq1119 : B1119.tree = HexagonCover.NBand.M8500_8700.SplitData.node1119 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1120

def B1118 : Block := .branch 165 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B1119, (.leaf 0 [] 0)]
theorem treeEq1118 : B1118.tree = HexagonCover.NBand.M8500_8700.SplitData.node1118 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1119
  · rfl

def B1117 : Block := .branch 167 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B1118, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1117 : B1117.tree = HexagonCover.NBand.M8500_8700.SplitData.node1117 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1118
  · rfl

def B1088 : Block := .branch 129 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1089, B1117, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1088 : B1088.tree = HexagonCover.NBand.M8500_8700.SplitData.node1088 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1089
  · exact treeEq1117
  · rfl
  · rfl

theorem accepted1088 : B1088.accepted = true := by decide +kernel
theorem checked1088 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1088 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1088]
  exact B1088.sound accepted1088
#print axioms checked1088

end HexagonCover.NBand.M8500_8700.SplitTree.Run0014
